package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.*;

public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;
	JavaClass original = null;
	JavaClass optimized = null;
	public ConstantFolder(String classFilePath)
	{
		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
		} catch(IOException e){
			e.printStackTrace();
		}
	}

	// Main entry to be called inside optimize()
	private void constant_var_fold(ClassGen cgen, ConstantPoolGen cpgen) {
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;
	
			System.out.println("\n[INFO] Analyzing method: " + method.getName());
	
			// Step 1: Find constant assignments
			Map<Integer, Number> constantVars = findConstantAssignments(il, cpgen);
			Set<Integer> reassigned = findReassignedVariables(il);
			for (Integer varIndex : reassigned) {
				if (constantVars.containsKey(varIndex)) {
					System.out.println("[DEBUG] Removing var_" + varIndex + " from constantVars (reassigned)");
					constantVars.remove(varIndex);
				}
			}
			System.out.println("[DEBUG] Final constant assignments: " + constantVars);
			replaceConstantLoads(il, cpgen, constantVars);

			boolean changed;
			do {
				changed = false;
				InstructionHandle current = il.getStart();
				while (current != null) {
					InstructionHandle next = tryFoldExpression(current, il, cpgen, constantVars);
					if (next != null) {
						changed = true;
						il.setPositions(true); 
					}
					current = (next != null) ? next : current.getNext();
				}
			} while (changed);

			if (il != null) {
				il.setPositions(true);
				mg.setMaxStack();
				mg.setMaxLocals();
			
				// Rebuild the method with updated StackMapTable
				Method newMethod = mg.getMethod(); // this triggers recomputation
				cgen.replaceMethod(method, newMethod);
			}
		}
	}

	private void redirectTargeters(InstructionHandle oldTarget, InstructionHandle newTarget) {
		if (oldTarget.hasTargeters()) {
			for (InstructionTargeter targeter : oldTarget.getTargeters()) {
				targeter.updateTarget(oldTarget, newTarget);
			}
		}
	}
	

	private void replaceWithConstant(InstructionList il,
                                 InstructionHandle from,
                                 InstructionHandle to,
                                 Number value,
                                 ConstantPoolGen cpgen) {
		try {
			// Create the correct constant instruction
			Instruction constInstr;
			if (value instanceof Integer) {
				constInstr = new LDC(cpgen.addInteger(value.intValue()));
			} else if (value instanceof Float) {
				constInstr = new LDC(cpgen.addFloat(value.floatValue()));
			} else if (value instanceof Long) {
				constInstr = new LDC2_W(cpgen.addLong(value.longValue()));
			} else if (value instanceof Double) {
				constInstr = new LDC2_W(cpgen.addDouble(value.doubleValue()));
			} else {
				System.out.println("[WARN] Unsupported constant type: " + value.getClass());
				return;
			}

			// Insert the constant before 'from'
			InstructionHandle inserted = il.insert(from, constInstr);

			// Redirect all targeters to the new constant
			for (InstructionHandle h = from; h != to.getNext(); h = h.getNext()) {
				redirectTargeters(h, inserted);
			}

			// Delete range cleanly
			il.delete(from, to);

			System.out.println("[DEBUG] Replaced instructions from " +
				from.getPosition() + " to " + to.getPosition() + " with constant " + value);
		} catch (TargetLostException e) {
			System.err.println("[ERROR] Failed to replace expression with constant: " + e.getMessage());
		}
	}

	private Number getConstantValue(InstructionHandle handle, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		Instruction inst = handle.getInstruction();
	
		// Case 1: Direct constants
		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			Object val = ((LDC) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LDC2_W) {
			Object val = ((LDC2_W) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		}
	
		// Case 2: Load from known constant variable
		if (inst instanceof LoadInstruction) {
			int index = ((LoadInstruction) inst).getIndex();
			return constants.get(index);
		}
	
		// Case 3: Try to evaluate binary expression recursively (e.g. a + 764, then * 3)
		InstructionHandle prev2 = handle.getPrev();
		InstructionHandle prev1 = (prev2 != null) ? prev2.getPrev() : null;
	
		if (prev1 != null && prev2 != null) {
			Instruction op     = inst;
			Number val1 = getConstantValue(prev1, cpgen, constants);
			Number val2 = getConstantValue(prev2, cpgen, constants);
	
			if (val1 == null || val2 == null) return null;
	
			if (op instanceof IADD) return val1.intValue() + val2.intValue();
			if (op instanceof ISUB) return val1.intValue() - val2.intValue();
			if (op instanceof IMUL) return val1.intValue() * val2.intValue();
			if (op instanceof IDIV && val2.intValue() != 0) return val1.intValue() / val2.intValue();
			if (op instanceof IREM && val2.intValue() != 0) return val1.intValue() % val2.intValue();
	
			if (op instanceof LADD) return val1.longValue() + val2.longValue();
			if (op instanceof LSUB) return val1.longValue() - val2.longValue();
			if (op instanceof LMUL) return val1.longValue() * val2.longValue();
			if (op instanceof LDIV && val2.longValue() != 0) return val1.longValue() / val2.longValue();
			if (op instanceof LREM && val2.longValue() != 0) return val1.longValue() % val2.longValue();
	
			if (op instanceof DADD) return val1.doubleValue() + val2.doubleValue();
			if (op instanceof DSUB) return val1.doubleValue() - val2.doubleValue();
			if (op instanceof DMUL) return val1.doubleValue() * val2.doubleValue();
			if (op instanceof DDIV && val2.doubleValue() != 0.0) return val1.doubleValue() / val2.doubleValue();
			if (op instanceof DREM && val2.doubleValue() != 0.0) return val1.doubleValue() % val2.doubleValue();
		}
		if (inst instanceof I2D) {
			InstructionHandle prev = handle.getPrev();
			if (prev != null) {
				Number val = getConstantValue(prev, cpgen, constants);
				if (val != null && val instanceof Integer) {
					return val.doubleValue(); 
				}
			}
		}
	
		// Not foldable
		return null;
	}

	private Number evaluateRecursive(InstructionHandle start, int depth, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		Instruction inst = start.getInstruction();

		// Handle cases like:
		if (inst instanceof DADD) {
			InstructionHandle i2dHandle = start.getPrev();
			if (i2dHandle == null) return null;

			Instruction i2d = i2dHandle.getInstruction();

			if (i2d instanceof I2D) {
				InstructionHandle intHandle = i2dHandle.getPrev();
				InstructionHandle doubleHandle = intHandle != null ? intHandle.getPrev() : null;

				if (intHandle == null || doubleHandle == null) return null;

				Number left = getConstantValue(doubleHandle, cpgen, constants);  // double
				Number right = getConstantValue(intHandle, cpgen, constants);    // int

				if (left != null && right != null) {
					double result = left.doubleValue() + right.doubleValue();
					return result;
				}
			}
		}
		
		if (start == null || depth > 5) return null;
	
		Number left = getConstantValue(start, cpgen, constants);
	
		if (left == null) {
			InstructionHandle leftStart = start.getPrev();
			if (leftStart == null || leftStart.getPrev() == null) return null;
	
			InstructionHandle op1 = leftStart;
			InstructionHandle op2 = leftStart.getNext();
			InstructionHandle op3 = op2 != null ? op2.getNext() : null;
	
			if (op3 == null || !(op3.getInstruction() instanceof ArithmeticInstruction)) return null;
	
			Number v1 = getConstantValue(op1, cpgen, constants); 
			Number v2 = getConstantValue(op2, cpgen, constants); 
			ArithmeticInstruction op = (ArithmeticInstruction) op3.getInstruction();
	
			if (v1 != null && v2 != null) {
				Number result = applyArithmetic(v1, v2, op);
				if (result != null) {
					constants.putIfAbsent(999 + depth, result); 
					return result;
				}
			}
			return null;
		}
		return left;
	}
	
	private Number applyArithmetic(Number v1, Number v2, ArithmeticInstruction op) {
		if (op instanceof IADD) return v1.intValue() + v2.intValue();
		if (op instanceof ISUB) return v1.intValue() - v2.intValue();
		if (op instanceof IMUL) return v1.intValue() * v2.intValue();
		if (op instanceof IDIV && v2.intValue() != 0) return v1.intValue() / v2.intValue();
		if (op instanceof IREM && v2.intValue() != 0) return v1.intValue() % v2.intValue();
	
		if (op instanceof LADD) return v1.longValue() + v2.longValue();
		if (op instanceof LSUB) return v1.longValue() - v2.longValue();
		if (op instanceof LMUL) return v1.longValue() * v2.longValue();
		if (op instanceof LDIV && v2.longValue() != 0) return v1.longValue() / v2.longValue();
		if (op instanceof LREM && v2.longValue() != 0) return v1.longValue() % v2.longValue();
	
		if (op instanceof FADD) return v1.floatValue() + v2.floatValue();
		if (op instanceof FSUB) return v1.floatValue() - v2.floatValue();
		if (op instanceof FMUL) return v1.floatValue() * v2.floatValue();
		if (op instanceof FDIV && v2.floatValue() != 0.0f) return v1.floatValue() / v2.floatValue();
		if (op instanceof FREM && v2.floatValue() != 0.0f) return v1.floatValue() % v2.floatValue();
	
		if (op instanceof DADD) return v1.doubleValue() + v2.doubleValue();
		if (op instanceof DSUB) return v1.doubleValue() - v2.doubleValue();
		if (op instanceof DMUL) return v1.doubleValue() * v2.doubleValue();
		if (op instanceof DDIV && v2.doubleValue() != 0.0) return v1.doubleValue() / v2.doubleValue();
		if (op instanceof DREM && v2.doubleValue() != 0.0) return v1.doubleValue() % v2.doubleValue();
	
		return null; // not supported
	}
	
	
	private InstructionHandle tryFoldExpression(InstructionHandle handle, InstructionList il, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		if (handle == null || handle.getNext() == null || handle.getNext().getNext() == null)
			return null;
	
		InstructionHandle h1 = handle;
		InstructionHandle h2 = h1.getNext();
		InstructionHandle h3 = h2.getNext();
	
		Instruction opInstr = h3.getInstruction();
		if (!(opInstr instanceof ArithmeticInstruction)) return null;
	
		Number result = evaluateRecursive(h3, 0, cpgen, constants);
		if (result == null) return null;
	
		System.out.println("[DEBUG] Folding chain starting at " + h1.getPosition() + ": result = " + result);
	
		// Save the next instruction after h3 before deletion
		InstructionHandle nextAfter = h3.getNext();
	
		// Replace with constant
		replaceWithConstant(il, h1, h3, result, cpgen);
	
		// If there's a store right after, assign the folded constant to the variable
		if (nextAfter != null && nextAfter.getInstruction() instanceof StoreInstruction) {
			StoreInstruction store = (StoreInstruction) nextAfter.getInstruction();
			constants.put(store.getIndex(), result);
			System.out.println("[DEBUG] Assigned folded result to var_" + store.getIndex());
			nextAfter = nextAfter.getNext(); // skip past store too
		}
	
		il.setPositions(true);
		return nextAfter; // resume after folded section
	}

	private Set<Integer> findReassignedVariables(InstructionList il) {
		Set<Integer> reassigned = new HashSet<>();
		Map<Integer, Boolean> seenOnce = new HashMap<>();
	
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();
	
			if (inst instanceof StoreInstruction) {
				int varIndex = ((StoreInstruction) inst).getIndex();
	
				if (!seenOnce.containsKey(varIndex)) {
					seenOnce.put(varIndex, true); // First time seeing store to this var
				} else {
					reassigned.add(varIndex);     // Seen more than once
				}
			}
		}
	
		return reassigned;
	}

	private Map<Integer, Number> findConstantAssignments(InstructionList il, ConstantPoolGen cpgen) {
		Map<Integer, Number> constants = new HashMap<>();
	
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();
			InstructionHandle next = handle.getNext();
			if (next == null) continue;
	
			Instruction nextInst = next.getInstruction();
	
			Number value = null;
			if (inst instanceof ConstantPushInstruction) {
				value = ((ConstantPushInstruction) inst).getValue();
			} else if (inst instanceof LDC) {
				Object cst = ((LDC) inst).getValue(cpgen);
				if (cst instanceof Number) value = (Number) cst;
			} else if (inst instanceof LDC2_W) {
				Object cst = ((LDC2_W) inst).getValue(cpgen);
				if (cst instanceof Number) value = (Number) cst;
			}
	
			if (value != null && nextInst instanceof StoreInstruction) {
				int varIndex = ((StoreInstruction) nextInst).getIndex();
				constants.put(varIndex, value);
				System.out.println("[DEBUG] Found constant assignment: var_" + varIndex + " = " + value);
			}
		}
	
		return constants;
	}	
	
	private void replaceConstantLoads(InstructionList il, ConstantPoolGen cpgen, Map<Integer, Number> constantVars) {
		for (InstructionHandle handle = il.getStart(); handle != null; ) {
			Instruction inst = handle.getInstruction();
	
			if (inst instanceof LoadInstruction) {
				int varIndex = ((LoadInstruction) inst).getIndex();
	
				// === ✨ Skip folding if used in conditional or branch logic ===
				InstructionHandle next = handle.getNext();
				if (next != null) {
					Instruction nextInst = next.getInstruction();
					if (
						nextInst instanceof IfInstruction ||
						nextInst instanceof LCMP ||
						nextInst instanceof FCMPG ||
						nextInst instanceof FCMPL ||
						nextInst instanceof DCMPG ||
						nextInst instanceof DCMPL
					) {
						handle = handle.getNext(); // skip folding
						continue;
					}
				}
	
				if (constantVars.containsKey(varIndex)) {
					Number value = constantVars.get(varIndex);
					Instruction replacement;
	
					// === Constant selection ===
					if (value instanceof Integer) {
						int intVal = value.intValue();
						if (intVal >= -1 && intVal <= 5) {
							replacement = new ICONST(intVal);
						} else if (intVal >= Byte.MIN_VALUE && intVal <= Byte.MAX_VALUE) {
							replacement = new BIPUSH((byte) intVal);
						} else if (intVal >= Short.MIN_VALUE && intVal <= Short.MAX_VALUE) {
							replacement = new SIPUSH((short) intVal);
						} else {
							replacement = new LDC(cpgen.addInteger(intVal));
						}
					} else if (value instanceof Float) {
						replacement = new LDC(cpgen.addFloat(value.floatValue()));
					} else if (value instanceof Long) {
						replacement = new LDC2_W(cpgen.addLong(value.longValue()));
					} else if (value instanceof Double) {
						replacement = new LDC2_W(cpgen.addDouble(value.doubleValue()));
					} else {
						System.out.println("[WARN] Unsupported constant type for var_" + varIndex);
						handle = handle.getNext();
						continue;
					}
	
					try {
						InstructionHandle newHandle = il.insert(handle, replacement);
						redirectTargeters(handle, newHandle);
						il.delete(handle);
						handle = newHandle.getNext();
						System.out.println("[DEBUG] Replaced load of var_" + varIndex + " with constant: " + value);
					} catch (TargetLostException e) {
						System.err.println("[ERROR] Target lost while replacing constant load: " + e.getMessage());
						handle = handle.getNext(); // skip on failure
					}
				} else {
					handle = handle.getNext(); // not a constant var
				}
			} else {
				handle = handle.getNext(); // not a load instruction
			}
		}
	}
	
	

	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		cgen.setMajor(50);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		try {
			constant_var_fold(cgen, cpgen);
			gen = cgen;
			this.optimized = gen.getJavaClass();
		} catch (Exception e) {
			System.err.println("[ERROR] Optimization failed:");
			e.printStackTrace();
		}
	}
	
	public void write(String optimisedFilePath)
	{
		this.optimize();
		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}