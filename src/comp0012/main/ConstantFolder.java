package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;
import org.apache.bcel.util.InstructionFinder;


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
	
	public void optimize()
	{
		ClassGen cgen = new ClassGen(original);
		ConstantPoolGen cpgen = cgen.getConstantPool();

		// Loop through all methods of the class
		for (Method method : cgen.getMethods()) {
			MethodGen mg = new MethodGen(method, cgen.getClassName(), cpgen);
			InstructionList il = mg.getInstructionList();
			if (il == null) continue;

			boolean changed = false;
			InstructionFinder f = new InstructionFinder(il);

			System.out.println("=== Constant Variable Folding: Identification & Propagation ===");

			Map<Integer, Object> constVars = new HashMap<>();
			Set<Integer> invalidatedVars = new HashSet<>();
			InstructionHandle[] handles = il.getInstructionHandles();

			for (int i = 0; i < handles.length; i++) {
				Instruction inst = handles[i].getInstruction();

				// === Case 1: Constant push (any kind) followed by STORE ===
				if (i + 1 < handles.length &&
					inst instanceof ConstantPushInstruction &&
					handles[i + 1].getInstruction() instanceof StoreInstruction) {

					Object value = ((ConstantPushInstruction) inst).getValue();
					int index = ((StoreInstruction) handles[i + 1].getInstruction()).getIndex();

					if (!invalidatedVars.contains(index)) {
						constVars.put(index, value);
						System.out.println("Constant assigned: var " + index + " = " + value);
					}

					i++; // Skip over store
				}

				// === Case 1b: LDC or LDC2_W followed by STORE ===
				else if (i + 1 < handles.length &&
					(inst instanceof LDC || inst instanceof LDC2_W) &&
					handles[i + 1].getInstruction() instanceof StoreInstruction) {

					Object value = (inst instanceof LDC)
						? ((LDC) inst).getValue(cpgen)
						: ((LDC2_W) inst).getValue(cpgen);

					int index = ((StoreInstruction) handles[i + 1].getInstruction()).getIndex();
					if (!invalidatedVars.contains(index)) {
						constVars.put(index, value);
						System.out.println("Constant assigned: var " + index + " = " + value);
					}

					i++;
				}

				// === Case 2: LOAD var, constant, arithmetic op, STORE ===
				else if (
					i + 3 < handles.length &&
					handles[i].getInstruction() instanceof LoadInstruction &&
					(handles[i + 1].getInstruction() instanceof ConstantPushInstruction ||
					handles[i + 1].getInstruction() instanceof LDC ||
					handles[i + 1].getInstruction() instanceof LDC2_W) &&
					handles[i + 2].getInstruction() instanceof ArithmeticInstruction &&
					handles[i + 3].getInstruction() instanceof StoreInstruction
				) {
					LoadInstruction load = (LoadInstruction) handles[i].getInstruction();
					int srcIndex = load.getIndex();
					Object constVal1 = constVars.get(srcIndex);

					Instruction constInst = handles[i + 1].getInstruction();
					Object constVal2 = null;
					if (constInst instanceof ConstantPushInstruction)
						constVal2 = ((ConstantPushInstruction) constInst).getValue();
					else if (constInst instanceof LDC)
						constVal2 = ((LDC) constInst).getValue(cpgen);
					else if (constInst instanceof LDC2_W)
						constVal2 = ((LDC2_W) constInst).getValue(cpgen);

					Instruction op = handles[i + 2].getInstruction();
					int destIndex = ((StoreInstruction) handles[i + 3].getInstruction()).getIndex();

					if (constVal1 instanceof Number && constVal2 instanceof Number) {
						Number n1 = (Number) constVal1;
						Number n2 = (Number) constVal2;
						Object result = null;

						if (op instanceof IADD) result = n1.intValue() + n2.intValue();
						else if (op instanceof ISUB) result = n1.intValue() - n2.intValue();
						else if (op instanceof IMUL) result = n1.intValue() * n2.intValue();
						else if (op instanceof IDIV && n2.intValue() != 0) result = n1.intValue() / n2.intValue();

						else if (op instanceof LADD) result = n1.longValue() + n2.longValue();
						else if (op instanceof LSUB) result = n1.longValue() - n2.longValue();
						else if (op instanceof LMUL) result = n1.longValue() * n2.longValue();
						else if (op instanceof LDIV && n2.longValue() != 0) result = n1.longValue() / n2.longValue();

						else if (op instanceof FADD) result = n1.floatValue() + n2.floatValue();
						else if (op instanceof FSUB) result = n1.floatValue() - n2.floatValue();
						else if (op instanceof FMUL) result = n1.floatValue() * n2.floatValue();
						else if (op instanceof FDIV && n2.floatValue() != 0) result = n1.floatValue() / n2.floatValue();

						else if (op instanceof DADD) result = n1.doubleValue() + n2.doubleValue();
						else if (op instanceof DSUB) result = n1.doubleValue() - n2.doubleValue();
						else if (op instanceof DMUL) result = n1.doubleValue() * n2.doubleValue();
						else if (op instanceof DDIV && n2.doubleValue() != 0) result = n1.doubleValue() / n2.doubleValue();

						if (result != null && !invalidatedVars.contains(destIndex)) {
							constVars.put(destIndex, result);
							System.out.println("Folded: var " + destIndex + " = " + result +
									" (from var " + srcIndex + " + const " + constVal2 + ")");
							i += 3;
							continue;
						}
					}
				}

				// === Case 3: Reassignment from unknown, invalidate ===
				else if (inst instanceof StoreInstruction) {
					int index = ((StoreInstruction) inst).getIndex();
					if (!constVars.containsKey(index)) {
						invalidatedVars.add(index);
						System.out.println("Invalidated var " + index + ": assigned non-constant");
					}
				}
			}

			System.out.println("=== Identification & Propagation Complete ===");

			for (InstructionHandle ih : il.getInstructionHandles()) {
				Instruction inst = ih.getInstruction();
			
				// Replace loads of constant variables with LDC
				if (inst instanceof LoadInstruction) {
					int index = ((LoadInstruction) inst).getIndex();
			
					if (constVars.containsKey(index)) {
						Object val = constVars.get(index);
						Instruction newInst = null;
			
						if (val instanceof Integer)
							newInst = new LDC(cpgen.addInteger((Integer) val));
						else if (val instanceof Float)
							newInst = new LDC(cpgen.addFloat((Float) val));
						else if (val instanceof Long)
							newInst = new LDC2_W(cpgen.addLong((Long) val));
						else if (val instanceof Double)
							newInst = new LDC2_W(cpgen.addDouble((Double) val));
						else if (val instanceof String)
							newInst = new LDC(cpgen.addString((String) val));
			
						if (newInst != null) {

								ih.setInstruction(newInst);
								System.out.println("Replaced use of var " + index + " with constant " + val);
						}
					}
				}
			}
			
			



			// Simple Folding START
			// Updated pattern to handle both LDC and LDC2_W
			String pattern = "(LDC|LDC2_W) (LDC|LDC2_W) (IADD|ISUB|IMUL|IDIV|LADD|LSUB|LMUL|LDIV|FADD|FSUB|FMUL|FDIV|DADD|DSUB|DMUL|DDIV)";
			for (Iterator<?> it = f.search(pattern); it.hasNext();) {
				InstructionHandle[] match = (InstructionHandle[]) it.next();

				Instruction inst1 = match[0].getInstruction();
				Instruction inst2 = match[1].getInstruction();
				Instruction opInst = match[2].getInstruction();

				// Process instructions when both are LDC (int or float)
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

						// Replace with a single LDC for int
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

						// Replace with a single LDC for float
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
				// Process instructions when both are LDC2_W (long or double)
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

						// Replace with a single LDC2_W for long
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

						// Replace with a single LDC2_W for double
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

			// If changes were made to the instructions, update the method
			if (changed) {
				mg.setInstructionList(il);
				mg.setMaxStack();
				mg.setMaxLocals();
				cgen.replaceMethod(method, mg.getMethod());
			}
		}

		gen = cgen;
	
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