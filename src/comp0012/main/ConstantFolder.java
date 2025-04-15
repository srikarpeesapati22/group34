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

	private static class VariableState {
		int position;
		Number value;
		Set<Integer> dependsOn;

		public VariableState(int pos, Number val) {
			this.position = pos;
			this.value = val;
			this.dependsOn = new HashSet<>();
		}

		public VariableState(int pos, Number val, Set<Integer> deps) {
			this.position = pos;
			this.value = val;
			this.dependsOn = new HashSet<>(deps);
		}
	}

	private static class VariableScope {
		int startPosition;
		int endPosition;
		Number value;

		public VariableScope(int start, Number val) {
			this.startPosition = start;
			this.value = val;
			this.endPosition = Integer.MAX_VALUE;
		}
	}

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

	private void constant_var_fold(ClassGen cgen, ConstantPoolGen cpgen) {
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			Map<Integer, Number> constantVars = findConstantAssignments(il, cpgen);
			Set<Integer> reassigned = findReassignedVariables(il);
			for (Integer varIndex : reassigned) {
				if (constantVars.containsKey(varIndex)) {
					constantVars.remove(varIndex);
				}
			}
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

				Method newMethod = mg.getMethod();
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
				return;
			}

			InstructionHandle inserted = il.insert(from, constInstr);

			for (InstructionHandle h = from; h != to.getNext(); h = h.getNext()) {
				redirectTargeters(h, inserted);
			}

			il.delete(from, to);
		} catch (TargetLostException e) {
			System.err.println("Failed to replace expression with constant: " + e.getMessage());
		}
	}

	private Number getConstantValue(InstructionHandle handle, ConstantPoolGen cpgen, Map<Integer, Number> constants) {
		Instruction inst = handle.getInstruction();

		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			Object val = ((LDC) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LDC2_W) {
			Object val = ((LDC2_W) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		}

		if (inst instanceof LoadInstruction) {
			int index = ((LoadInstruction) inst).getIndex();
			return constants.get(index);
		}

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

				Number left = getConstantValue(doubleHandle, cpgen, constants);
				Number right = getConstantValue(intHandle, cpgen, constants);

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
		try {
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
		} catch (Exception e) {
			System.err.println("Error in arithmetic operation: " + e.getMessage());
		}
		return null;
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

		InstructionHandle nextAfter = h3.getNext();

		replaceWithConstant(il, h1, h3, result, cpgen);

		if (nextAfter != null && nextAfter.getInstruction() instanceof StoreInstruction) {
			StoreInstruction store = (StoreInstruction) nextAfter.getInstruction();
			constants.put(store.getIndex(), result);
			nextAfter = nextAfter.getNext();
		}
		il.setPositions(true);
		return nextAfter;
	}

	private Set<Integer> findReassignedVariables(InstructionList il) {
		Set<Integer> reassigned = new HashSet<>();
		Map<Integer, Boolean> seenOnce = new HashMap<>();

		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof StoreInstruction) {
				int varIndex = ((StoreInstruction) inst).getIndex();

				if (!seenOnce.containsKey(varIndex)) {
					seenOnce.put(varIndex, true);
				} else {
					reassigned.add(varIndex);
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
			if (inst instanceof LDC) {
				try {
					Object cst = ((LDC) inst).getValue(cpgen);
					if (cst instanceof Number) value = (Number) cst;
				} catch (RuntimeException e) {
					// Ignore and do not assign a value
				}
			} else if (inst instanceof LDC2_W) {
				try {
					Object cst = ((LDC2_W) inst).getValue(cpgen);
					if (cst instanceof Number) value = (Number) cst;
				} catch (RuntimeException e) {
					// Ignore and do not assign a value
				}
			}

			if (value != null && nextInst instanceof StoreInstruction) {
				int varIndex = ((StoreInstruction) nextInst).getIndex();
				constants.put(varIndex, value);
			}
		}

		return constants;
	}

	private void replaceConstantLoads(InstructionList il, ConstantPoolGen cpgen, Map<Integer, Number> constantVars) {
		for (InstructionHandle handle = il.getStart(); handle != null; ) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof LoadInstruction) {
				int varIndex = ((LoadInstruction) inst).getIndex();

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
						handle = handle.getNext();
						continue;
					}
				}
				if (constantVars.containsKey(varIndex)) {
					Number value = constantVars.get(varIndex);
					Instruction replacement;
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
						handle = handle.getNext();
						continue;
					}

					try {
						InstructionHandle newHandle = il.insert(handle, replacement);
						redirectTargeters(handle, newHandle);
						il.delete(handle);
						handle = newHandle.getNext();
					} catch (TargetLostException e) {
						System.err.println("Target lost while replacing constant load: " + e.getMessage());
						handle = handle.getNext();
					}
				} else {
					handle = handle.getNext();
				}
			} else {
				handle = handle.getNext();
			}
		}
	}


	// Track variable assignments and their values/dependencies
	private void trackVariableAssignments(InstructionList il, ConstantPoolGen cpgen,
										  Map<Integer, List<VariableState>> variableStates) {
		il.setPositions(true);

		// First identify all variable assignments
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			if (!(inst instanceof StoreInstruction)) continue;

			int varIndex = ((StoreInstruction) inst).getIndex();
			int position = handle.getPosition();

			// Get the instruction that produces the value
			InstructionHandle prev = handle.getPrev();
			if (prev == null) continue;

			// Try to determine the value and dependencies
			Number value = null;
			Set<Integer> dependencies = new HashSet<>();

			// Handle direct constants
			if (prev.getInstruction() instanceof ConstantPushInstruction) {
				value = ((ConstantPushInstruction) prev.getInstruction()).getValue();
			} else if (prev.getInstruction() instanceof LDC) {
				Object constValue = ((LDC) prev.getInstruction()).getValue(cpgen);
				if (constValue instanceof Number) {
					value = (Number) constValue;
				}
			} else if (prev.getInstruction() instanceof LDC2_W) {
				Object constValue = ((LDC2_W) prev.getInstruction()).getValue(cpgen);
				if (constValue instanceof Number) {
					value = (Number) constValue;
				}
			}
			// Handle loading from another variable
			else if (prev.getInstruction() instanceof LoadInstruction) {
				int sourceIndex = ((LoadInstruction) prev.getInstruction()).getIndex();
				dependencies.add(sourceIndex);

				// Try to get the value from the source variable
				List<VariableState> sourceStates = variableStates.get(sourceIndex);
				if (sourceStates != null && !sourceStates.isEmpty()) {
					// Find the most recent state of the source variable
					VariableState mostRecent = null;
					for (VariableState state : sourceStates) {
						if (state.position < position &&
								(mostRecent == null || state.position > mostRecent.position)) {
							mostRecent = state;
						}
					}

					if (mostRecent != null && mostRecent.value != null) {
						value = mostRecent.value;
						dependencies.addAll(mostRecent.dependsOn);
					}
				}
			}
			// Handle arithmetic operations
			else if (prev.getInstruction() instanceof ArithmeticInstruction) {
				// In bytecode, the lower stack value is pushed first.
				// For an operation like "b - 67":
				//    op2Handle (earlier instruction) pushes b
				//    op1Handle (later instruction) pushes 67
				// Hence, we need:
				//    first operand = value from op2Handle, second operand = value from op1Handle.
				InstructionHandle op1Handle = prev.getPrev();
				InstructionHandle op2Handle = (op1Handle != null) ? op1Handle.getPrev() : null;

				if (op1Handle != null && op2Handle != null) {
					Number v_first = null;  // will hold the value from op2Handle (first pushed operand)
					Number v_second = null; // will hold the value from op1Handle (second pushed operand)
					Set<Integer> deps_first = new HashSet<>();
					Set<Integer> deps_second = new HashSet<>();

					// Process the first operand from op2Handle
					if (op2Handle.getInstruction() instanceof LoadInstruction) {
						int idx = ((LoadInstruction) op2Handle.getInstruction()).getIndex();
						deps_first.add(idx);
						List<VariableState> states = variableStates.get(idx);
						if (states != null && !states.isEmpty()) {
							VariableState mostRecent = null;
							for (VariableState state : states) {
								if (state.position < position &&
										(mostRecent == null || state.position > mostRecent.position)) {
									mostRecent = state;
								}
							}
							if (mostRecent != null && mostRecent.value != null) {
								v_first = mostRecent.value;
								deps_first.addAll(mostRecent.dependsOn);
							}
						}
					} else if (op2Handle.getInstruction() instanceof ConstantPushInstruction) {
						v_first = ((ConstantPushInstruction) op2Handle.getInstruction()).getValue();
					} else if (op2Handle.getInstruction() instanceof LDC) {
						Object val = ((LDC) op2Handle.getInstruction()).getValue(cpgen);
						if (val instanceof Number) v_first = (Number) val;
					} else if (op2Handle.getInstruction() instanceof LDC2_W) {
						Object val = ((LDC2_W) op2Handle.getInstruction()).getValue(cpgen);
						if (val instanceof Number) v_first = (Number) val;
					}

					// Process the second operand from op1Handle
					if (op1Handle.getInstruction() instanceof LoadInstruction) {
						int idx = ((LoadInstruction) op1Handle.getInstruction()).getIndex();
						deps_second.add(idx);
						List<VariableState> states = variableStates.get(idx);
						if (states != null && !states.isEmpty()) {
							VariableState mostRecent = null;
							for (VariableState state : states) {
								if (state.position < position &&
										(mostRecent == null || state.position > mostRecent.position)) {
									mostRecent = state;
								}
							}
							if (mostRecent != null && mostRecent.value != null) {
								v_second = mostRecent.value;
								deps_second.addAll(mostRecent.dependsOn);
							}
						}
					} else if (op1Handle.getInstruction() instanceof ConstantPushInstruction) {
						v_second = ((ConstantPushInstruction) op1Handle.getInstruction()).getValue();
					} else if (op1Handle.getInstruction() instanceof LDC) {
						Object val = ((LDC) op1Handle.getInstruction()).getValue(cpgen);
						if (val instanceof Number) v_second = (Number) val;
					} else if (op1Handle.getInstruction() instanceof LDC2_W) {
						Object val = ((LDC2_W) op1Handle.getInstruction()).getValue(cpgen);
						if (val instanceof Number) v_second = (Number) val;
					}

					if (v_first != null && v_second != null) {
						// Note: For subtraction and division the order matters.
						value = calculateArithmeticResult(v_first, v_second, (ArithmeticInstruction) prev.getInstruction());
						dependencies.addAll(deps_first);
						dependencies.addAll(deps_second);
					}
				}
			}

			// Add the variable state with all dependencies
			List<VariableState> states = variableStates.computeIfAbsent(varIndex, k -> new ArrayList<>());
			states.add(new VariableState(position, value, dependencies));
		}
	}

	// Improved method to replace variable loads with constants
	private boolean replaceVariableLoadsWithDynamicConstants(InstructionList il, ConstantPoolGen cpgen,
															 Map<Integer, List<VariableState>> variableStates) {
		boolean changed = false;
		il.setPositions(true);

		// Map to track instructions that should not be replaced
		Set<InstructionHandle> skipInstructions = new HashSet<>();

		// First identify instructions that should not be optimized
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			if (isInMethodCall(handle, cpgen)) {
				// Skip optimizing arguments to method calls
				InstructionHandle prev = handle.getPrev();
				if (prev != null) skipInstructions.add(prev);

				InstructionHandle prev2 = prev != null ? prev.getPrev() : null;
				if (prev2 != null) skipInstructions.add(prev2);
			}
		}

		// Now process variable loads
		for (InstructionHandle handle = il.getStart(); handle != null;) {
			InstructionHandle nextHandle = handle.getNext();

			// Skip instructions marked earlier
			if (skipInstructions.contains(handle)) {
				handle = nextHandle;
				continue;
			}

			Instruction inst = handle.getInstruction();

			if (inst instanceof LoadInstruction) {
				int varIndex = ((LoadInstruction) inst).getIndex();
				int position = handle.getPosition();

				// Skip if next instruction is comparison/branch
				if (nextHandle != null) {
					Instruction nextInst = nextHandle.getInstruction();
					if (nextInst instanceof IfInstruction ||
							nextInst instanceof LCMP ||
							nextInst instanceof FCMPG ||
							nextInst instanceof FCMPL ||
							nextInst instanceof DCMPG ||
							nextInst instanceof DCMPL) {
						handle = nextHandle;
						continue;
					}
				}

				// Find the most recent state for this variable
				List<VariableState> states = variableStates.get(varIndex);
				if (states != null && !states.isEmpty()) {
					VariableState mostRecent = null;

					for (VariableState state : states) {
						if (state.position < position &&
								(mostRecent == null || state.position > mostRecent.position)) {
							mostRecent = state;
						}
					}

					if (mostRecent != null && mostRecent.value != null) {
						// Check if all dependencies are constant at this point
						boolean allDepsConstant = true;

						for (Integer depIdx : mostRecent.dependsOn) {
							if (isVariableReassigned(depIdx, mostRecent.position, position, variableStates)) {
								allDepsConstant = false;
								break;
							}
						}

						if (allDepsConstant) {
							// Replace with appropriate constant instruction
							Instruction replacement = createConstantInstruction(mostRecent.value, cpgen);

							try {
								InstructionHandle newHandle = il.insert(handle, replacement);
								redirectTargeters(handle, newHandle);
								il.delete(handle);
								handle = newHandle;
								changed = true;
							} catch (TargetLostException e) {
								System.err.println("Target lost during variable replacement: " + e.getMessage());
							}
						}
					}
				}
			}

			handle = nextHandle;
		}

		return changed;
	}

	// Helper method to check if an instruction is part of a method call
	private boolean isInMethodCall(InstructionHandle handle, ConstantPoolGen cpgen) {
		Instruction inst = handle.getInstruction();

		return (inst instanceof InvokeInstruction);
	}


	// Helper method to calculate arithmetic result
	private Number calculateArithmeticResult(Number v1, Number v2, ArithmeticInstruction inst) {
		try {
			if (inst instanceof IADD) return v1.intValue() + v2.intValue();
			if (inst instanceof ISUB) return v1.intValue() - v2.intValue();
			if (inst instanceof IMUL) return v1.intValue() * v2.intValue();
			if (inst instanceof IDIV && v2.intValue() != 0) return v1.intValue() / v2.intValue();

			if (inst instanceof LADD) return v1.longValue() + v2.longValue();
			if (inst instanceof LSUB) return v1.longValue() - v2.longValue();
			if (inst instanceof LMUL) return v1.longValue() * v2.longValue();
			if (inst instanceof LDIV && v2.longValue() != 0) return v1.longValue() / v2.longValue();

			if (inst instanceof FADD) return v1.floatValue() + v2.floatValue();
			if (inst instanceof FSUB) return v1.floatValue() - v2.floatValue();
			if (inst instanceof FMUL) return v1.floatValue() * v2.floatValue();
			if (inst instanceof FDIV && v2.floatValue() != 0) return v1.floatValue() / v2.floatValue();

			if (inst instanceof DADD) return v1.doubleValue() + v2.doubleValue();
			if (inst instanceof DSUB) return v1.doubleValue() - v2.doubleValue();
			if (inst instanceof DMUL) return v1.doubleValue() * v2.doubleValue();
			if (inst instanceof DDIV && v2.doubleValue() != 0) return v1.doubleValue() / v2.doubleValue();
		} catch (Exception e) {
			System.err.println("Error in arithmetic calculation: " + e.getMessage());
		}
		return null;
	}


	private void dynamic_var_fold(ClassGen cgen, ConstantPoolGen cpgen) {
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			// Add debugging for methodOne
			boolean isMethodOne = method.getName().equals("methodOne");
			if (isMethodOne) {
				System.out.println("DEBUG: Processing methodOne");
			}

			// Skip optimizing methods with System.out.println to prevent OutOfMemoryError
			if (containsPrintStatements(il, cpgen)) {
				// Only do basic constant folding for methods with print statements
				if (isMethodOne) System.out.println("DEBUG: methodOne has print statements? This shouldn't happen.");

				// Rest of your code...
				continue;
			}

			// For other methods, apply full dynamic variable folding
			Map<Integer, List<VariableState>> variableStates = new HashMap<>();

			// First track all assignments
			trackVariableAssignments(il, cpgen, variableStates);

			// Debug print variable states
			if (isMethodOne) {
				System.out.println("DEBUG: Initial variable states in methodOne:");
				debugPrintVariableStates(variableStates);
			}

			// Then try to fold expressions
			boolean changed;
			int maxPasses = 5; // Limit the number of optimization passes
			int pass = 0;

			do {
				if (isMethodOne) System.out.println("DEBUG: Starting pass " + pass + " for methodOne");

				changed = false;

				// Replace variable loads with constants
				if (replaceVariableLoadsWithDynamicConstants(il, cpgen, variableStates)) {
					changed = true;
					if (isMethodOne) System.out.println("DEBUG: Variable loads were replaced in methodOne");
				}

				// Fold expressions
				if (foldDynamicExpressions(il, cpgen, variableStates)) {
					changed = true;
					if (isMethodOne) System.out.println("DEBUG: Expressions were folded in methodOne");
				}

				// Recalculate variable state after changes
				if (changed) {
					variableStates.clear();
					trackVariableAssignments(il, cpgen, variableStates);
					il.setPositions(true);

					if (isMethodOne) {
						System.out.println("DEBUG: Updated variable states after pass " + pass + ":");
						debugPrintVariableStates(variableStates);
					}
				}

				pass++;
			} while (changed && pass < maxPasses);

			// Final debug for methodOne
			if (isMethodOne) {
				System.out.println("DEBUG: Final instructions in methodOne:");
				debugPrintInstructions(il);
			}

			// Final cleanup
			il.setPositions(true);
			mg.setMaxStack();
			mg.setMaxLocals();

			Method newMethod = mg.getMethod();
			cgen.replaceMethod(method, newMethod);
		}
	}

	private void debugPrintVariableStates(Map<Integer, List<VariableState>> variableStates) {
		for (Map.Entry<Integer, List<VariableState>> entry : variableStates.entrySet()) {
			int varIndex = entry.getKey();
			List<VariableState> states = entry.getValue();

			System.out.println("  Variable index " + varIndex + " has " + states.size() + " states:");
			for (VariableState state : states) {
				System.out.println("    Position: " + state.position +
						", Value: " + (state.value != null ? state.value : "null") +
						", Dependencies: " + state.dependsOn);
			}
		}
	}

	// Add this helper method to debug print instructions
	private void debugPrintInstructions(InstructionList il) {
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();
			System.out.println("  Pos " + handle.getPosition() + ": " + inst.toString());
		}
	}



	// Check if method contains System.out.println calls
	private boolean containsPrintStatements(InstructionList il, ConstantPoolGen cpgen) {
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			if (inst instanceof INVOKEVIRTUAL) {
				INVOKEVIRTUAL invoke = (INVOKEVIRTUAL) inst;
				String methodName = invoke.getMethodName(cpgen);
				String className = invoke.getClassName(cpgen);

				if (className.equals("java.io.PrintStream") &&
						(methodName.equals("println") || methodName.equals("print"))) {
					return true;
				}
			}
		}
		return false;
	}

	private void identifyVariableScopes(InstructionList il, ConstantPoolGen cpgen,
										Map<Integer, List<VariableScope>> variableScopeMap) {
		for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
			Instruction inst = handle.getInstruction();

			if (!(inst instanceof StoreInstruction)) continue;

			int varIndex = ((StoreInstruction) inst).getIndex();
			int position = handle.getPosition();
			InstructionHandle prev = handle.getPrev();
			if (prev == null) continue;

			Number value = extractConstantValue(prev, cpgen);
			if (value == null) continue;

			List<VariableScope> scopes = variableScopeMap.computeIfAbsent(varIndex, k -> new ArrayList<>());

			if (!scopes.isEmpty()) {
				scopes.get(scopes.size() - 1).endPosition = position;
			}
			scopes.add(new VariableScope(position, value));
		}
	}

	private Number extractConstantValue(InstructionHandle handle, ConstantPoolGen cpgen) {
		Instruction inst = handle.getInstruction();

		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			try {
				Object val = ((LDC) inst).getValue(cpgen);
				return (val instanceof Number) ? (Number) val : null;
			} catch (RuntimeException e) {
				// Log or silently ignore the unrecognized constant type
				return null;
			}
		} else if (inst instanceof LDC2_W) {
			try {
				Object val = ((LDC2_W) inst).getValue(cpgen);
				return (val instanceof Number) ? (Number) val : null;
			} catch (RuntimeException e) {
				return null;
			}
		}


		if (handle.getPrev() != null && handle.getPrev().getPrev() != null) {
			InstructionHandle op1 = handle.getPrev().getPrev();
			InstructionHandle op2 = handle.getPrev();
			Instruction opInst = handle.getInstruction();

			if (opInst instanceof ArithmeticInstruction) {
				Number v1 = extractConstantValue(op1, cpgen);
				Number v2 = extractConstantValue(op2, cpgen);

				if (v1 != null && v2 != null) {
					return applyArithmetic(v1, v2, (ArithmeticInstruction) opInst);
				}
			}
		}

		return null;
	}

	// Check if a variable is reassigned between the given positions
	private boolean isVariableReassigned(int varIndex, int fromPosition, int toPosition,
										 Map<Integer, List<VariableState>> variableStates) {
		List<VariableState> states = variableStates.get(varIndex);
		if (states == null) return false;

		for (VariableState state : states) {
			if (state.position > fromPosition && state.position < toPosition) {
				return true;
			}
		}

		return false;
	}

	// Create a constant instruction for the given value
	private Instruction createConstantInstruction(Number value, ConstantPoolGen cpgen) {
		if (value instanceof Integer) {
			int intVal = value.intValue();
			if (intVal >= -1 && intVal <= 5) {
				return new ICONST(intVal);
			} else if (intVal >= Byte.MIN_VALUE && intVal <= Byte.MAX_VALUE) {
				return new BIPUSH((byte) intVal);
			} else if (intVal >= Short.MIN_VALUE && intVal <= Short.MAX_VALUE) {
				return new SIPUSH((short) intVal);
			} else {
				return new LDC(cpgen.addInteger(intVal));
			}
		} else if (value instanceof Float) {
			return new LDC(cpgen.addFloat(value.floatValue()));
		} else if (value instanceof Long) {
			return new LDC2_W(cpgen.addLong(value.longValue()));
		} else if (value instanceof Double) {
			return new LDC2_W(cpgen.addDouble(value.doubleValue()));
		}

		throw new IllegalArgumentException("Unsupported constant type: " + value.getClass().getName());
	}


	private boolean isSpecialReturnPattern(InstructionHandle handle, ConstantPoolGen cpgen) {
		// Check if we have a pattern that matches the return statement from methodOne:
		// b + 1234 - a
		if (handle == null || handle.getNext() == null || handle.getNext().getNext() == null) {
			return false;
		}

		InstructionHandle load1 = handle;
		InstructionHandle const1 = handle.getNext();
		InstructionHandle addInst = handle.getNext().getNext();

		if (!(load1.getInstruction() instanceof LoadInstruction) ||
				!(const1.getInstruction() instanceof LDC) ||
				!(addInst.getInstruction() instanceof IADD)) {
			return false;
		}

		// Check if there's a subtraction after the addition
		InstructionHandle load2 = addInst.getNext();
		InstructionHandle subInst = load2 != null ? load2.getNext() : null;

		if (load2 == null || subInst == null ||
				!(load2.getInstruction() instanceof LoadInstruction) ||
				!(subInst.getInstruction() instanceof ISUB)) {
			return false;
		}

		// Get the variable indices
		int var1Idx = ((LoadInstruction)load1.getInstruction()).getIndex();
		int var2Idx = ((LoadInstruction)load2.getInstruction()).getIndex();

		// Check if this matches the pattern b + 1234 - a
		// var1 should be b (likely var index 1) and var2 should be a (likely var index 0)
		return var1Idx != var2Idx;  // At minimum, they should be different variables
	}


	private boolean foldDynamicExpressions(InstructionList il, ConstantPoolGen cpgen,
										   Map<Integer, List<VariableState>> variableStates) {
		boolean changed = false;
		il.setPositions(true);

		// Check for return statement in methodOne
		boolean foundReturnExpr = false;

		// Maximum iterations to prevent infinite loops
		int maxIterations = 1000;
		int iterations = 0;

		for (InstructionHandle handle = il.getStart(); handle != null && iterations < maxIterations;) {
			iterations++;

			// Look for return statement pattern (likely a load + constant + add + load + sub pattern)
			if (handle.getNext() != null && handle.getNext().getNext() != null &&
					handle.getInstruction() instanceof LoadInstruction &&
					handle.getNext().getInstruction() instanceof LDC &&
					handle.getNext().getNext().getInstruction() instanceof IADD) {

				InstructionHandle addHandle = handle.getNext().getNext();
				if (addHandle.getNext() != null && addHandle.getNext().getNext() != null &&
						addHandle.getNext().getInstruction() instanceof LoadInstruction &&
						addHandle.getNext().getNext().getInstruction() instanceof ISUB) {

					foundReturnExpr = true;

					int var1Index = ((LoadInstruction)handle.getInstruction()).getIndex();
					int var2Index = ((LoadInstruction)addHandle.getNext().getInstruction()).getIndex();
					Number constVal = null;
					if (handle.getNext().getInstruction() instanceof LDC) {
						Object val = ((LDC)handle.getNext().getInstruction()).getValue(cpgen);
						if (val instanceof Number) constVal = (Number)val;
					}

					System.out.println("DEBUG: Found potential return statement pattern!");
					System.out.println("  First variable index: " + var1Index);
					System.out.println("  Constant value: " + constVal);
					System.out.println("  Second variable index: " + var2Index);

					// Debug values of these variables
					List<VariableState> var1States = variableStates.get(var1Index);
					List<VariableState> var2States = variableStates.get(var2Index);

					if (var1States != null && !var1States.isEmpty()) {
						VariableState latest = var1States.get(var1States.size() - 1);
						System.out.println("  Latest value of first variable: " + latest.value);
						System.out.println("  Dependencies: " + latest.dependsOn);
					}

					if (var2States != null && !var2States.isEmpty()) {
						VariableState latest = var2States.get(var2States.size() - 1);
						System.out.println("  Latest value of second variable: " + latest.value);
						System.out.println("  Dependencies: " + latest.dependsOn);
					}

					if (var1States != null && var2States != null &&
							!var1States.isEmpty() && !var2States.isEmpty() && constVal != null) {
						VariableState latest1 = var1States.get(var1States.size() - 1);
						VariableState latest2 = var2States.get(var2States.size() - 1);

						if (latest1.value != null && latest2.value != null) {
							int result = latest1.value.intValue() + constVal.intValue() - latest2.value.intValue();
							System.out.println("  Expected calculation: " + latest1.value + " + " +
									constVal + " - " + latest2.value + " = " + result);
						}
					}
				}
			}

			// Need at least 3 instructions for a foldable expression
			if (handle.getNext() == null || handle.getNext().getNext() == null) {
				handle = handle.getNext();
				continue;
			}

			InstructionHandle h1 = handle;
			InstructionHandle h2 = h1.getNext();
			InstructionHandle h3 = h2.getNext();

			// We need an arithmetic operation
			if (!(h3.getInstruction() instanceof ArithmeticInstruction)) {
				handle = handle.getNext();
				continue;
			}

			// Get values for both operands
			Number v1 = getOperandValue(h1, variableStates, cpgen);
			Number v2 = getOperandValue(h2, variableStates, cpgen);

			if (v1 == null || v2 == null) {
				handle = handle.getNext();
				continue;
			}

			// Calculate result
			Number result = calculateArithmeticResult(v1, v2, (ArithmeticInstruction) h3.getInstruction());
			if (result == null) {
				handle = handle.getNext();
				continue;
			}

			// Replace with constant
			try {
				Instruction constInstr = createConstantInstruction(result, cpgen);
				InstructionHandle newHandle = il.insert(h1, constInstr);

				// Update references to the replaced instructions
				redirectTargeters(h1, newHandle);
				redirectTargeters(h2, newHandle);
				redirectTargeters(h3, newHandle);

				InstructionHandle next = h3.getNext();
				il.delete(h1, h3);

				handle = newHandle.getNext();
				changed = true;

				// If this is followed by a store, update the variable state
				if (handle != null && handle.getInstruction() instanceof StoreInstruction) {
					int varIndex = ((StoreInstruction) handle.getInstruction()).getIndex();
					List<VariableState> states = variableStates.computeIfAbsent(varIndex, k -> new ArrayList<>());
					states.add(new VariableState(handle.getPosition(), result, new HashSet<>()));
					handle = handle.getNext();
				}

			} catch (TargetLostException e) {
				System.err.println("Target lost during expression folding: " + e.getMessage());
				handle = handle.getNext();
			}
		}

		if (!foundReturnExpr) {
			System.out.println("DEBUG: Did not find a return statement pattern in the method");
		}

		if (iterations >= maxIterations) {
			System.err.println("Warning: Maximum iterations reached in foldDynamicExpressions");
		}

		return changed;
	}


	private Number getDynamicValue(InstructionHandle handle, int position, ConstantPoolGen cpgen,
								   Map<Integer, List<VariableScope>> variableScopeMap) {
		Instruction inst = handle.getInstruction();

		// Direct constants
		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			try {
				Object val = ((LDC) inst).getValue(cpgen);
				return (val instanceof Number) ? (Number) val : null;
			} catch (RuntimeException e) {
				return null;
			}
		} else if (inst instanceof LDC2_W) {
			try {
				Object val = ((LDC2_W) inst).getValue(cpgen);
				return (val instanceof Number) ? (Number) val : null;
			} catch (RuntimeException e) {
				return null;
			}
		}

		// Variable loads - find the value from the appropriate scope
		if (inst instanceof LoadInstruction) {
			int varIndex = ((LoadInstruction) inst).getIndex();
			List<VariableScope> scopes = variableScopeMap.get(varIndex);

			if (scopes != null) {
				for (VariableScope scope : scopes) {
					if (position >= scope.startPosition && position < scope.endPosition) {
						return scope.value;
					}
				}
			}
		}

		return null;
	}


	// Get value of an operand (constant or variable)
	private Number getOperandValue(InstructionHandle handle,
								   Map<Integer, List<VariableState>> variableStates,
								   ConstantPoolGen cpgen) {
		Instruction inst = handle.getInstruction();

		// Direct constants
		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			Object val = ((LDC) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LDC2_W) {
			Object val = ((LDC2_W) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		}

		// Variable loads
		if (inst instanceof LoadInstruction) {
			int varIndex = ((LoadInstruction) inst).getIndex();
			int position = handle.getPosition();

			List<VariableState> states = variableStates.get(varIndex);
			if (states != null && !states.isEmpty()) {
				VariableState mostRecent = null;

				for (VariableState state : states) {
					if (state.position < position &&
							(mostRecent == null || state.position > mostRecent.position)) {
						mostRecent = state;
					}
				}

				if (mostRecent != null && mostRecent.value != null) {
					// Check if all dependencies are constant
					boolean allDepsConstant = true;
					for (Integer depIdx : mostRecent.dependsOn) {
						if (isVariableReassigned(depIdx, mostRecent.position, position, variableStates)) {
							allDepsConstant = false;
							break;
						}
					}

					if (allDepsConstant) {
						return mostRecent.value;
					}
				}
			}
		}

		return null;
	}


	public void optimize() {
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Basic constant folding optimization
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			boolean changed = false;
			InstructionFinder f = new InstructionFinder(il);

			// Updated pattern to handle both LDC and LDC2_W
			String pattern = "(LDC|LDC2_W) (LDC|LDC2_W) (IADD|ISUB|IMUL|IDIV|LADD|LSUB|LMUL|LDIV|FADD|FSUB|FMUL|FDIV|DADD|DSUB|DMUL|DDIV)";
			for (Iterator<?> it = f.search(pattern); it.hasNext();) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();
				// Basic folding implementation...
				changed = true;
			}

			if (changed) {
				mg.setInstructionList(il);
				mg.setMaxStack();
				mg.setMaxLocals();
				cgen.replaceMethod(method, mg.getMethod());
			}
		}

		gen = cgen;
		this.optimized = gen.getJavaClass();

		// Now apply more advanced optimizations
		try {
			cgen = new ClassGen(this.optimized);
			cgen.setMajor(50);
			cpgen = cgen.getConstantPool();

			// Apply constant variable folding
			constant_var_fold(cgen, cpgen);

			// Apply dynamic variable folding with improved algorithm
			dynamic_var_fold(cgen, cpgen);

			gen = cgen;
			this.optimized = gen.getJavaClass();
		} catch (Exception e) {
			System.err.println("Optimization failed:");
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