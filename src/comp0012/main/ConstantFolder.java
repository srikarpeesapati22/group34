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
		}
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
	
				if (constantVars.containsKey(varIndex)) {
					Number value = constantVars.get(varIndex);
					Instruction replacement;
	
					// Choose appropriate constant push instruction
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
						il.delete(handle);
						handle = newHandle.getNext(); // safely move on
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