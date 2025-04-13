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
	
			// Step 1: Track constant assignments
			Map<Integer, Number> constantVars = findConstantAssignments(il, cpgen);
			Set<Integer> reassigned = findReassignedVariables(il);

			// Remove reassigned variables from constant folding
			for (Integer varIndex : reassigned) {
				if (constantVars.containsKey(varIndex)) {
					System.out.println("[INFO] Removing var_" + varIndex + " from constants due to reassignment.");
					constantVars.remove(varIndex);
				}
			}
	
			// Step 2: Find and store all replacements first
			List<InstructionHandle> handlesToReplace = new ArrayList<>();

			for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
				Instruction inst = handle.getInstruction();

				if (inst instanceof LoadInstruction) {
					LoadInstruction load = (LoadInstruction) inst;
					int varIndex = load.getIndex();

					if (constantVars.containsKey(varIndex)) {
						handlesToReplace.add(handle);
					}
				}
			}

			// Step 3: Perform replacements after scanning
			for (InstructionHandle handle : handlesToReplace) {
				LoadInstruction load = (LoadInstruction) handle.getInstruction();
				int varIndex = load.getIndex();
				Number value = constantVars.get(varIndex);

				System.out.println("[DEBUG] Found load of constant var_" + varIndex + " at position " +
								handle.getPosition() + ", replacing with value: " + value);

				replaceWithConstant(il, handle, handle, value, cpgen);
			}

			InstructionHandle current = il.getStart();
			while (current != null) {
				InstructionHandle next = tryFoldExpression(current, il, cpgen, constantVars);
				current = (next != null) ? next : current.getNext();
			}
	
			// Finalize method and apply
			mg.setMaxStack();
			mg.setMaxLocals();
			cgen.replaceMethod(method, mg.getMethod());
		}
	}

	// Helper to check and track constants assigned to local variables
	private Map<Integer, Number> findConstantAssignments(InstructionList il, ConstantPoolGen cpgen) {
		Map<Integer, Number> constantVars = new HashMap<>();

		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			// Detect constants being pushed
			if (inst instanceof ConstantPushInstruction) {
				ConstantPushInstruction push = (ConstantPushInstruction) inst;
				Number value = push.getValue();
				InstructionHandle next = handle.getNext();

				if (next != null && next.getInstruction() instanceof StoreInstruction) {
					StoreInstruction store = (StoreInstruction) next.getInstruction();
					int varIndex = store.getIndex();

					// Log detected assignment
					System.out.println("[DEBUG] Constant assignment detected: var_" + varIndex + " = " + value);

					constantVars.put(varIndex, value);
					handle = next; // skip over the store
				}
			}

			// Detect ldc (Object-wrapped constants from pool)
			else if (inst instanceof LDC) {
				LDC ldc = (LDC) inst;
				Object cst = ldc.getValue(cpgen);
				if (cst instanceof Number) {
					Number value = (Number) cst;
					InstructionHandle next = handle.getNext();

					if (next != null && next.getInstruction() instanceof StoreInstruction) {
						StoreInstruction store = (StoreInstruction) next.getInstruction();
						int varIndex = store.getIndex();

						System.out.println("[DEBUG] Constant assignment detected via LDC: var_" + varIndex + " = " + value);

						constantVars.put(varIndex, value);
						handle = next;
					}
				}
			}

			// Detect ldc2_w (for long and double)
			else if (inst instanceof LDC2_W) {
				LDC2_W ldc2 = (LDC2_W) inst;
				Object cst = ldc2.getValue(cpgen);
				if (cst instanceof Number) {
					Number value = (Number) cst;
					InstructionHandle next = handle.getNext();

					if (next != null && next.getInstruction() instanceof StoreInstruction) {
						StoreInstruction store = (StoreInstruction) next.getInstruction();
						int varIndex = store.getIndex();

						System.out.println("[DEBUG] Constant assignment detected via LDC2_W: var_" + varIndex + " = " + value);

						constantVars.put(varIndex, value);
						handle = next;
					}
				}
			}
		}

		System.out.println("[DEBUG] Final constant assignments: " + constantVars);
		return constantVars;
	}

	// Helper to find variables that are reassigned (and thus non-constant)
	private Set<Integer> findReassignedVariables(InstructionList il) {
		Set<Integer> reassigned = new HashSet<>();
		Map<Integer, Integer> firstSeenStore = new HashMap<>();

		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof StoreInstruction) {
				StoreInstruction store = (StoreInstruction) inst;
				int varIndex = store.getIndex();

				if (!firstSeenStore.containsKey(varIndex)) {
					firstSeenStore.put(varIndex, handle.getPosition());
				} else {
					reassigned.add(varIndex);
					System.out.println("[DEBUG] Variable var_" + varIndex +
							" is reassigned at instruction position " + handle.getPosition());
				}
			}
		}

		System.out.println("[DEBUG] Reassigned variables: " + reassigned);
		return reassigned;
	}

	// Helper to fold constant usages using tracked constant variables
	//private void foldConstants(MethodGen mg, InstructionList il, ConstantPoolGen cpgen, Map<Integer, Number> constants) {}

	// Utility: Tries to fold a sequence of instructions starting from a load using known constants
	private InstructionHandle tryFoldExpression(InstructionHandle handle, InstructionList il, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		Instruction inst1 = handle.getInstruction();
		InstructionHandle next1 = handle.getNext();
		if (next1 == null) return null;
	
		Instruction inst2 = next1.getInstruction();
		InstructionHandle next2 = next1.getNext();
		if (next2 == null) return null;
	
		Instruction inst3 = next2.getInstruction();
	
		Number val1 = null;
		Number val2 = null;
	
		// --- Step 1: Load first operand ---
		val1 = getConstantValue(inst1, cpgen, constants);
		if (val1 == null) return null;
	
		// --- Step 2: Load second operand ---
		val2 = getConstantValue(inst2, cpgen, constants);
		if (val2 == null) return null;
	
		// --- Step 3: Arithmetic folding ---
		Number result = null;
	
		// INT
		if (inst3 instanceof IADD) result = val1.intValue() + val2.intValue();
		else if (inst3 instanceof ISUB) result = val1.intValue() - val2.intValue();
		else if (inst3 instanceof IMUL) result = val1.intValue() * val2.intValue();
		else if (inst3 instanceof IDIV && val2.intValue() != 0) result = val1.intValue() / val2.intValue();
		else if (inst3 instanceof IREM && val2.intValue() != 0) result = val1.intValue() % val2.intValue();
	
		// LONG
		else if (inst3 instanceof LADD) result = val1.longValue() + val2.longValue();
		else if (inst3 instanceof LSUB) result = val1.longValue() - val2.longValue();
		else if (inst3 instanceof LMUL) result = val1.longValue() * val2.longValue();
		else if (inst3 instanceof LDIV && val2.longValue() != 0) result = val1.longValue() / val2.longValue();
		else if (inst3 instanceof LREM && val2.longValue() != 0) result = val1.longValue() % val2.longValue();
	
		// DOUBLE
		else if (inst3 instanceof DADD) result = val1.doubleValue() + val2.doubleValue();
		else if (inst3 instanceof DSUB) result = val1.doubleValue() - val2.doubleValue();
		else if (inst3 instanceof DMUL) result = val1.doubleValue() * val2.doubleValue();
		else if (inst3 instanceof DDIV && val2.doubleValue() != 0.0) result = val1.doubleValue() / val2.doubleValue();
		else if (inst3 instanceof DREM && val2.doubleValue() != 0.0) result = val1.doubleValue() % val2.doubleValue();
	
		// Unsupported or divide by zero
		if (result == null) return null;
	
		System.out.println("[DEBUG] Folding expression at " + handle.getPosition() + ": " +
				val1 + " " + inst3.getName() + " " + val2 + " = " + result);
	
		replaceWithConstant(il, handle, next2, result, cpgen);
		return next2.getNext();
	}
	
	private Number getConstantValue(Instruction inst, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			Object val = ((LDC) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LDC2_W) {
			Object val = ((LDC2_W) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LoadInstruction) {
			int index = ((LoadInstruction) inst).getIndex();
			return constants.getOrDefault(index, null);
		}
		return null;
	}

	// Utility: Replaces an expression with a constant (e.g., ldc 3650)
	private void replaceWithConstant(InstructionList il, InstructionHandle from, InstructionHandle to, Number value, ConstantPoolGen cpgen) {
		try {
			// Cache positions BEFORE deletion
			int fromPos = from.getPosition();
			int toPos = to.getPosition();
	
			// Create instruction for the constant
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
	
			// Insert before 'from'
			il.insert(from, constInstr);
	
			// Delete full range from 'from' to 'to'
			InstructionHandle current = from;
			while (current != to) {
				InstructionHandle next = current.getNext();
				il.delete(current);
				current = next;
			}
			il.delete(to); // delete last one
	
			System.out.println("[DEBUG] Replaced instructions from " + fromPos + " to " + toPos + " with constant: " + value);
		} catch (TargetLostException e) {
			System.err.println("[ERROR] Target lost while replacing instructions: " + e.getMessage());
		}
	}

	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		constant_var_fold(cgen, cpgen);

        
		this.optimized = gen.getJavaClass();
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