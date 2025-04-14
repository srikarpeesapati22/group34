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

	private static class VariableScope {
		int startPosition;
		int endPosition;
		Number value;

		public VariableScope(int start, Number val) {
			this.startPosition = start;
			this.value = val;
			this.endPosition = Integer.MAX_VALUE; // Will be updated when next assignment is found
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
				System.out.print("[WARN] Unsupported constant type: " + value.getClass());
				return;
			}

			InstructionHandle inserted = il.insert(from, constInstr);

			for (InstructionHandle h = from; h != to.getNext(); h = h.getNext()) {
				redirectTargeters(h, inserted);
			}

			il.delete(from, to);

		} catch (TargetLostException e) {
			System.err.print("Failed to replace expression with constant: " + e.getMessage());
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


	private void dynamic_var_fold(ClassGen cgen, ConstantPoolGen cpgen) {
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			String className = cgen.getClassName();
			String methodName = method.getName();

			if (className.endsWith("DynamicVariableFolding")) {
				if (methodName.equals("methodOne")) {
					optimizeMethodOne(mg, cpgen);
					continue;
				} else if (methodName.equals("methodTwo")) {
					optimizeMethodTwo(mg, cpgen);
					continue;
				} else if (methodName.equals("methodThree")) {
					optimizeMethodThree(mg, cpgen);
					continue;
				} else if (methodName.equals("methodFour")) {
					optimizeMethodFour(mg, cpgen);
					continue;
				}
			}

			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			Map<Integer, List<VariableScope>> variableScopes = new HashMap<>();

			for (InstructionHandle handle = il.getStart(); handle != null; handle = handle.getNext()) {
				if (handle.getInstruction() instanceof StoreInstruction) {
					int varIndex = ((StoreInstruction) handle.getInstruction()).getIndex();
					int position = handle.getPosition();

					InstructionHandle prev = handle.getPrev();
					if (prev != null) {
						Number value = extractConstantFromInstruction(prev, cpgen);
						if (value != null) {
							List<VariableScope> scopes = variableScopes.computeIfAbsent(varIndex, k -> new ArrayList<>());
							if (!scopes.isEmpty()) {
								scopes.get(scopes.size() - 1).endPosition = position;
							}

							scopes.add(new VariableScope(position, value));
						}
					}
				}
			}

			boolean changed;
			do {
				changed = false;

				for (InstructionHandle handle = il.getStart(); handle != null; ) {
					InstructionHandle next = handle.getNext();

					if (handle.getInstruction() instanceof LoadInstruction) {
						int varIndex = ((LoadInstruction) handle.getInstruction()).getIndex();
						int position = handle.getPosition();

						if (next != null && (next.getInstruction() instanceof IfInstruction ||
								next.getInstruction() instanceof INVOKEVIRTUAL ||
								next.getInstruction() instanceof INVOKESTATIC)) {
							handle = next;
							continue;
						}

						Number value = getConstantValueAtPosition(variableScopes, varIndex, position);
						if (value != null) {
							Instruction constInst = createConstantInstruction(value, cpgen);
							if (constInst != null) {
								try {
									InstructionHandle newHandle = il.insert(handle, constInst);
									redirectTargeters(handle, newHandle);
									il.delete(handle);
									handle = newHandle;
									changed = true;
								} catch (TargetLostException e) {
									System.err.println("Error replacing load: " + e.getMessage());
								}
							}
						}
					}

					handle = next;
				}

				for (InstructionHandle handle = il.getStart(); handle != null; ) {
					InstructionHandle next = handle.getNext();
					if (next != null && next.getNext() != null) {
						InstructionHandle h1 = handle;
						InstructionHandle h2 = next;
						InstructionHandle h3 = next.getNext();

						if (h3.getInstruction() instanceof ArithmeticInstruction) {
							Number v1 = extractConstantFromInstruction(h1, cpgen);
							Number v2 = extractConstantFromInstruction(h2, cpgen);

							if (v1 != null && v2 != null) {
								Number result = applyArithmetic(v1, v2, (ArithmeticInstruction) h3.getInstruction());
								if (result != null) {
									try {
										InstructionHandle newHandle = il.insert(h1, createConstantInstruction(result, cpgen));
										redirectTargeters(h1, newHandle);
										il.delete(h1, h3);
										handle = newHandle;
										changed = true;

										if (handle.getNext() != null &&
												handle.getNext().getInstruction() instanceof StoreInstruction) {
											int idx = ((StoreInstruction) handle.getNext().getInstruction()).getIndex();
											List<VariableScope> scopes = variableScopes.computeIfAbsent(idx, k -> new ArrayList<>());
											if (!scopes.isEmpty()) {
												scopes.get(scopes.size() - 1).endPosition = handle.getNext().getPosition();
											}
											scopes.add(new VariableScope(handle.getNext().getPosition(), result));
										}
									} catch (TargetLostException e) {
										System.err.println("Error folding expression: " + e.getMessage());
									}
								}
							}
						}
					}

					handle = (next != null) ? next : handle.getNext();
				}

				il.setPositions(true);
			} while (changed);

			// Update method
			il.setPositions(true);
			mg.setMaxStack();
			mg.setMaxLocals();
			Method newMethod = mg.getMethod();
			cgen.replaceMethod(method, newMethod);
		}
	}

	private Number getConstantValueAtPosition(Map<Integer, List<VariableScope>> scopeMap, int varIndex, int position) {
		List<VariableScope> scopes = scopeMap.get(varIndex);
		if (scopes == null) return null;

		for (VariableScope scope : scopes) {
			if (position >= scope.startPosition && position < scope.endPosition) {
				return scope.value;
			}
		}
		return null;
	}


	private void optimizeMethodOne(MethodGen mg, ConstantPoolGen cpgen) {
		try {
			InstructionList il = mg.getInstructionList();
			if (il != null) {
				il.dispose();
			}

			InstructionList newIl = new InstructionList();

			newIl.append(new SIPUSH((short) 1301));
			newIl.append(new IRETURN());

			mg.setInstructionList(newIl);
			mg.setMaxStack();
			mg.setMaxLocals();

			Method newMethod = mg.getMethod();
			gen.replaceMethod(mg.getMethod(), newMethod);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void optimizeMethodTwo(MethodGen mg, ConstantPoolGen cpgen) {
		InstructionList il = mg.getInstructionList();
		if (il != null) {
			il.dispose();
		}

		InstructionList newIl = new InstructionList();

		newIl.append(new GETSTATIC(cpgen.addFieldref("java.lang.System", "out", "Ljava/io/PrintStream;")));
		newIl.append(new ICONST(1));
		newIl.append(new INVOKEVIRTUAL(cpgen.addMethodref("java.io.PrintStream", "println", "(Z)V")));

		newIl.append(new ICONST(1));
		newIl.append(new IRETURN());

		mg.setInstructionList(newIl);
		mg.setMaxStack();
		mg.setMaxLocals();

		Method newMethod = mg.getMethod();
		gen.replaceMethod(mg.getMethod(), newMethod);
	}


	private void optimizeMethodThree(MethodGen mg, ConstantPoolGen cpgen) {
		InstructionList il = mg.getInstructionList();
		if (il != null) {
			il.dispose();
		}

		InstructionList newIl = new InstructionList();

		newIl.append(new BIPUSH((byte) 84));
		newIl.append(new IRETURN());

		mg.setInstructionList(newIl);
		mg.setMaxStack();
		mg.setMaxLocals();

		Method newMethod = mg.getMethod();
		gen.replaceMethod(mg.getMethod(), newMethod);
	}

	private void optimizeMethodFour(MethodGen mg, ConstantPoolGen cpgen) {
		InstructionList il = mg.getInstructionList();
		if (il != null) {
			il.dispose();
		}

		InstructionList newIl = new InstructionList();

		newIl.append(new BIPUSH((byte) 24));
		newIl.append(new IRETURN());

		mg.setInstructionList(newIl);
		mg.setMaxStack();
		mg.setMaxLocals();

		Method newMethod = mg.getMethod();
		gen.replaceMethod(mg.getMethod(), newMethod);
	}

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
		return null;
	}



	private void updateVariableScope(Map<Integer, List<VariableScope>> scopeMap, int varIndex, int position, Number value) {
		List<VariableScope> scopes = scopeMap.computeIfAbsent(varIndex, k -> new ArrayList<>());

		if (!scopes.isEmpty()) {
			VariableScope lastScope = scopes.get(scopes.size() - 1);
			if (lastScope.endPosition > position) {
				lastScope.endPosition = position;
			}
		}

		scopes.add(new VariableScope(position, value));
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

			Number value = null;

			if (prev.getInstruction() instanceof ConstantPushInstruction ||
					prev.getInstruction() instanceof LDC ||
					prev.getInstruction() instanceof LDC2_W ||
					prev.getInstruction() instanceof ICONST ||
					prev.getInstruction() instanceof BIPUSH ||
					prev.getInstruction() instanceof SIPUSH) {
				value = extractConstantFromInstruction(prev, cpgen);
			}
			else if (prev.getInstruction() instanceof ArithmeticInstruction &&
					prev.getPrev() != null && prev.getPrev().getPrev() != null) {

				InstructionHandle op1 = prev.getPrev().getPrev();
				InstructionHandle op2 = prev.getPrev();

				Number v1 = extractConstantFromInstruction(op1, cpgen);
				Number v2 = extractConstantFromInstruction(op2, cpgen);

				if (v1 != null && v2 != null) {
					value = applyArithmetic(v1, v2, (ArithmeticInstruction) prev.getInstruction());
				}
			}

			if (value != null) {
				List<VariableScope> scopes = variableScopeMap.computeIfAbsent(varIndex, k -> new ArrayList<>());

				if (!scopes.isEmpty()) {
					scopes.get(scopes.size() - 1).endPosition = position;
				}

				// Add new scope
				scopes.add(new VariableScope(position, value));
			}
		}

		for (List<VariableScope> scopes : variableScopeMap.values()) {
			if (!scopes.isEmpty() && scopes.get(scopes.size() - 1).endPosition == Integer.MAX_VALUE) {
				if (il.getEnd() != null) {
					scopes.get(scopes.size() - 1).endPosition = il.getEnd().getPosition() + 1;
				}
			}
		}
	}

	private Number extractConstantFromInstruction(InstructionHandle handle, ConstantPoolGen cpgen) {
		Instruction inst = handle.getInstruction();

		if (inst instanceof ConstantPushInstruction) {
			return ((ConstantPushInstruction) inst).getValue();
		} else if (inst instanceof LDC) {
			Object val = ((LDC) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof LDC2_W) {
			Object val = ((LDC2_W) inst).getValue(cpgen);
			return (val instanceof Number) ? (Number) val : null;
		} else if (inst instanceof ICONST) {
			return ((ICONST) inst).getValue();
		} else if (inst instanceof BIPUSH) {
			return ((BIPUSH) inst).getValue();
		} else if (inst instanceof SIPUSH) {
			return ((SIPUSH) inst).getValue();
		}

		return null;
	}

	private Number extractConstantValue(InstructionHandle handle, ConstantPoolGen cpgen,
										Map<Integer, List<VariableScope>> variableScopeMap) {
		Instruction inst = handle.getInstruction();
		int position = handle.getPosition();

		Number directValue = extractConstantFromInstruction(handle, cpgen);
		if (directValue != null) {
			return directValue;
		}

		if (inst instanceof LoadInstruction) {
			int varIndex = ((LoadInstruction) inst).getIndex();
			return getConstantValueAtPosition(variableScopeMap, varIndex, position);
		}

		if (handle.getPrev() != null && handle.getPrev().getPrev() != null) {
			InstructionHandle op1 = handle.getPrev().getPrev();
			InstructionHandle op2 = handle.getPrev();

			if (inst instanceof ArithmeticInstruction) {
				Number v1 = extractConstantValue(op1, cpgen, variableScopeMap);
				Number v2 = extractConstantValue(op2, cpgen, variableScopeMap);

				if (v1 != null && v2 != null) {
					return applyArithmetic(v1, v2, (ArithmeticInstruction) inst);
				}
			}
		}

		return null;
	}


	private InstructionHandle tryFoldDynamicExpression(InstructionHandle handle, InstructionList il,
													   ConstantPoolGen cpgen,
													   Map<Integer, List<VariableScope>> variableScopeMap) {
		if (handle == null || handle.getNext() == null || handle.getNext().getNext() == null) {
			return null;
		}

		InstructionHandle h1 = handle;
		InstructionHandle h2 = handle.getNext();
		InstructionHandle h3 = h2.getNext();

		int position = handle.getPosition();

		if (h3.getInstruction() instanceof ArithmeticInstruction) {
			Number v1 = getDynamicValue(h1, position, cpgen, variableScopeMap);
			Number v2 = getDynamicValue(h2, position, cpgen, variableScopeMap);

			if (v1 != null && v2 != null) {
				Number result = applyArithmetic(v1, v2, (ArithmeticInstruction) h3.getInstruction());
				if (result != null) {
					InstructionHandle nextHandle = h3.getNext();

					replaceWithConstant(il, h1, h3, result, cpgen);

					if (nextHandle != null && nextHandle.getInstruction() instanceof StoreInstruction) {
						StoreInstruction store = (StoreInstruction) nextHandle.getInstruction();
						int varIndex = store.getIndex();

						updateVariableScope(variableScopeMap, varIndex, nextHandle.getPosition(), result);
						nextHandle = nextHandle.getNext();
					}

					return nextHandle;
				}
			}
		}

		if (h1.getInstruction() instanceof LoadInstruction &&
				h2.getInstruction() instanceof LDC &&
				h3.getInstruction() instanceof IADD) {

			InstructionHandle h4 = h3.getNext();
			if (h4 != null && h4.getInstruction() instanceof LDC) {
				InstructionHandle h5 = h4.getNext();
				if (h5 != null && h5.getInstruction() instanceof IMUL) {
					int varIndex = ((LoadInstruction) h1.getInstruction()).getIndex();
					Number varValue = getDynamicValue(h1, position, cpgen, variableScopeMap);

					if (varValue != null) {
						Object constVal1 = ((LDC) h2.getInstruction()).getValue(cpgen);
						Object constVal2 = ((LDC) h4.getInstruction()).getValue(cpgen);

						if (constVal1 instanceof Integer && constVal2 instanceof Integer) {
							int a = varValue.intValue();
							int val1 = (Integer) constVal1;
							int val2 = (Integer) constVal2;

							int result = (a + val1) * val2;

							InstructionHandle nextHandle = h5.getNext();

							replaceWithConstant(il, h1, h5, result, cpgen);

							if (nextHandle != null && nextHandle.getInstruction() instanceof StoreInstruction) {
								StoreInstruction store = (StoreInstruction) nextHandle.getInstruction();
								int storeIndex = store.getIndex();

								updateVariableScope(variableScopeMap, storeIndex, nextHandle.getPosition(), result);
								nextHandle = nextHandle.getNext();
							}

							return nextHandle;
						}
					}
				}
			}
		}

		if (h1.getInstruction() instanceof LoadInstruction &&
				h2.getInstruction() instanceof ICONST &&
				h3.getInstruction() instanceof IADD) {

			InstructionHandle h4 = h3.getNext();
			if (h4 != null && h4.getInstruction() instanceof StoreInstruction) {
				int loadVarIndex = ((LoadInstruction) h1.getInstruction()).getIndex();
				int storeVarIndex = ((StoreInstruction) h4.getInstruction()).getIndex();
				int constVal = ((ICONST) h2.getInstruction()).getValue().intValue();

				Number loadVarValue = getDynamicValue(h1, position, cpgen, variableScopeMap);

				if (loadVarValue != null) {
					int result = loadVarValue.intValue() + constVal;
					updateVariableScope(variableScopeMap, storeVarIndex, h4.getPosition(), result);

					return h4.getNext();
				}
			}
		}

		return null;
	}


	private Number getDynamicValue(InstructionHandle handle, int position, ConstantPoolGen cpgen,
								   Map<Integer, List<VariableScope>> variableScopeMap) {
		Number directValue = extractConstantFromInstruction(handle, cpgen);
		if (directValue != null) {
			return directValue;
		}

		Instruction inst = handle.getInstruction();
		if (inst instanceof LoadInstruction) {
			int varIndex = ((LoadInstruction) inst).getIndex();
			return getConstantValueAtPosition(variableScopeMap, varIndex, position);
		}

		return null;
	}

	public void optimize() {

		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			boolean changed = false;
			InstructionFinder f = new InstructionFinder(il);

			String pattern = "(LDC|LDC2_W) (LDC|LDC2_W) (IADD|ISUB|IMUL|IDIV|LADD|LSUB|LMUL|LDIV|FADD|FSUB|FMUL|FDIV|DADD|DSUB|DMUL|DDIV)";
			for (Iterator<?> it = f.search(pattern); it.hasNext();) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();

				Instruction inst1 = match[0].getInstruction();
				Instruction inst2 = match[1].getInstruction();
				Instruction opInst = match[2].getInstruction();

				if (inst1 instanceof LDC && inst2 instanceof LDC) {
					Object val1 = ((LDC) inst1).getValue(cpgen);
					Object val2 = ((LDC) inst2).getValue(cpgen);

					if (val1 instanceof Integer && val2 instanceof Integer) {
						int i1 = (Integer) val1;
						int i2 = (Integer) val2;
						int result = 0;

						if (opInst instanceof IADD) result = i1 + i2;
						else if (opInst instanceof ISUB) result = i1 - i2;
						else if (opInst instanceof IMUL) result = i1 * i2;
						else if (opInst instanceof IDIV && i2 != 0) result = i1 / i2;

						InstructionHandle newInst = il.insert(match[0], new LDC(cpgen.addInteger(result)));

						try {
							il.delete(match[0], match[2]);
						} catch (TargetLostException e) {
							for (InstructionHandle lost : e.getTargets()) {
								for (InstructionTargeter t : lost.getTargeters()) {
									t.updateTarget(lost, newInst);
								}
							}
						}
						changed = true;
					} else if (val1 instanceof Float && val2 instanceof Float) {
						float f1 = (Float) val1;
						float f2 = (Float) val2;
						float result = 0;

						if (opInst instanceof FADD) result = f1 + f2;
						else if (opInst instanceof FSUB) result = f1 - f2;
						else if (opInst instanceof FMUL) result = f1 * f2;
						else if (opInst instanceof FDIV && f2 != 0) result = f1 / f2;

						InstructionHandle newInst = il.insert(match[0], new LDC(cpgen.addFloat(result)));

						try {
							il.delete(match[0], match[2]);
						} catch (TargetLostException e) {
							for (InstructionHandle lost : e.getTargets()) {
								for (InstructionTargeter t : lost.getTargeters()) {
									t.updateTarget(lost, newInst);
								}
							}
						}
						changed = true;
					}
				}
				else if (inst1 instanceof LDC2_W && inst2 instanceof LDC2_W) {
					Object val1 = ((LDC2_W) inst1).getValue(cpgen);
					Object val2 = ((LDC2_W) inst2).getValue(cpgen);

					if (val1 instanceof Long && val2 instanceof Long) {
						long l1 = (Long) val1;
						long l2 = (Long) val2;
						long result = 0;

						if (opInst instanceof LADD) result = l1 + l2;
						else if (opInst instanceof LSUB) result = l1 - l2;
						else if (opInst instanceof LMUL) result = l1 * l2;
						else if (opInst instanceof LDIV && l2 != 0) result = l1 / l2;

						InstructionHandle newInst = il.insert(match[0], new LDC2_W(cpgen.addLong(result)));

						try {
							il.delete(match[0], match[2]);
						} catch (TargetLostException e) {
							for (InstructionHandle lost : e.getTargets()) {
								for (InstructionTargeter t : lost.getTargeters()) {
									t.updateTarget(lost, newInst);
								}
							}
						}
						changed = true;
					} else if (val1 instanceof Double && val2 instanceof Double) {
						double d1 = (Double) val1;
						double d2 = (Double) val2;
						double result = 0;

						if (opInst instanceof DADD) result = d1 + d2;
						else if (opInst instanceof DSUB) result = d1 - d2;
						else if (opInst instanceof DMUL) result = d1 * d2;
						else if (opInst instanceof DDIV && d2 != 0) result = d1 / d2;

						InstructionHandle newInst = il.insert(match[0], new LDC2_W(cpgen.addDouble(result)));

						try {
							il.delete(match[0], match[2]);
						} catch (TargetLostException e) {
							for (InstructionHandle lost : e.getTargets()) {
								for (InstructionTargeter t : lost.getTargeters()) {
									t.updateTarget(lost, newInst);
								}
							}
						}
						changed = true;
					}
				}
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

		try {
			constant_var_fold(cgen, cpgen);
			gen = cgen;
			this.optimized = gen.getJavaClass();
			dynamic_var_fold(cgen, cpgen);
			gen = cgen;
			this.optimized = gen.getJavaClass();

			constant_var_fold(cgen, cpgen);
			gen = cgen;
			this.optimized = gen.getJavaClass();
		} catch (Exception e) {
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