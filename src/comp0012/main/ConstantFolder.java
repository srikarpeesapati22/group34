package comp0012.main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Iterator;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.DADD;
import org.apache.bcel.generic.DDIV;
import org.apache.bcel.generic.DMUL;
import org.apache.bcel.generic.DSUB;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.LADD;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LDIV;
import org.apache.bcel.generic.LMUL;
import org.apache.bcel.generic.LSUB;
import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.TargetLostException;



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