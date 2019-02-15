/**
 * 
 */
package edu.upenn.seas.precise.verisig;

import com.picklingtools.pickle.Pickler;
import com.picklingtools.pythonesque.Arr;
import com.picklingtools.pythonesque.Tab;
import com.verivital.hyst.grammar.formula.*;
import com.verivital.hyst.ir.AutomatonExportException;
import com.verivital.hyst.ir.base.AutomatonMode;
import com.verivital.hyst.ir.base.AutomatonTransition;
import com.verivital.hyst.ir.base.BaseComponent;
import com.verivital.hyst.ir.base.ExpressionInterval;
import com.verivital.hyst.passes.basic.SubstituteConstantsPass;
import com.verivital.hyst.printers.ToolPrinter;
import com.verivital.hyst.util.*;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.Option;

import java.io.IOException;
import java.util.*;
import java.util.Map.Entry;

/**
 * Printer for Flow* models. Based on Chris' Boogie printer.
 * 
 * @author Stanley Bak (8-2014)
 *
 */
public class VerisigPrinter extends ToolPrinter
{
	FlowstarExpressionPrinter flowstarExpressionPrinter;

	private BaseComponent ha;
	private Tab plant;

	private int modeIndex = 1;
	private HashMap<String, Integer> nameIndexMapping;

	public VerisigPrinter()
	{
		preconditions = new Preconditions(true);

		plant = new Tab();
		nameIndexMapping = new HashMap<>();
	}

	@Override
	protected String getCommentPrefix()
	{
		return "#";
	}

	/**
	 * This method starts the actual printing! Prepares variables etc. and calls printProcedure() to
	 * print the BPL code
	 */
	private void printDocument(String originalFilename)
	{
		printProcedure();
	}

	/**
	 * Simplify an expression by substituting constants and then doing math simplification
	 * 
	 *            the original expression
	 * @return the modified expression
	 */
	private Expression simplifyExpression(Expression ex)
	{
		Expression subbed = SubstituteConstantsPass.substituteConstantsIntoExpression(ha.constants,
				ex);

		return AutomatonUtil.simplifyExpression(subbed);
	}

	/**
	 * Print the actual Flow* code
	 */
	private void printProcedure()
	{
		//printVars();


	}

	/***
	 * Print variable declarations and their initial value assignments plus a list of all constants
	 */
	private void printVars()
	{
		boolean first = true;

		for (String v : ha.variables)
		{

		}
	}

	/**
	 * Prints the locations with their labels and everything that happens in them (invariant,
	 * flow...)
	 */
	private void printModes()
	{
		for (Entry<String, AutomatonMode> e : ha.modes.entrySet())
		{
			AutomatonMode mode = e.getValue();

			String locName = e.getKey();
			nameIndexMapping.put(locName, modeIndex);

			Tab modeTab = new Tab();
			plant.put(modeIndex, modeTab);
			modeTab.put("name", locName.trim());

			if (isNonLinearDynamics(mode.flowDynamics))
				modeTab.put("odetype","nonpoly ode");
			else if (Classification.isLinearDynamics(mode.flowDynamics))
				modeTab.put("odetype","linear ode");
			else if (ha.variables.size() <= 3)
				modeTab.put("odetype","poly ode 1");
			else if (ha.variables.size() <= 6)
				modeTab.put("odetype","poly ode 2");
			else
				modeTab.put("odetype","poly ode 3");

			// first simplify
			for (Entry<String, ExpressionInterval> entry : mode.flowDynamics.entrySet())
			{
				ExpressionInterval ei = entry.getValue();
				ei.setExpression(simplifyExpression(ei.getExpression()));
			}

			Tab dynamics = new Tab();
			modeTab.put("dynamics", dynamics);
			for (Entry<String, ExpressionInterval> entry : mode.flowDynamics.entrySet())
			{
				ExpressionInterval ei = entry.getValue();

				dynamics.put(entry.getKey(), (entry.getKey() + "\' = " + ei).trim());
			}


			Arr invariants = new Arr();
			modeTab.put("invariants", invariants);
			Expression inv = simplifyExpression(mode.invariant);

			if (!inv.equals(Constant.TRUE))
			{
				String s = inv.toString();
				String[] invars = s.split("&");

				for (String invar : invars) {
					invariants.add(invar.trim());
				}
			}

			modeIndex++;
		}
	}

	private boolean isNonLinearDynamics(LinkedHashMap<String, ExpressionInterval> flowDynamics)
	{
		boolean rv = false;

		for (ExpressionInterval entry : flowDynamics.values())
		{
			Expression e = entry.getExpression();

			byte classification = AutomatonUtil.classifyExpressionOps(e);

			if ((classification & AutomatonUtil.OPS_NONLINEAR) != 0)
			{
				rv = true;
				break;
			}
		}

		return rv;
	}

	private void printJumps()
	{
		for (AutomatonTransition t : ha.transitions)
		{
			Expression guard = simplifyExpression(t.guard);

			if (guard == Constant.FALSE)
				continue;

			String fromName = t.from.name;
			String toName = t.to.name;

			Integer fromModeIndex = nameIndexMapping.get(fromName);
			Integer toModeIndex = nameIndexMapping.get(toName);

			if( fromModeIndex == null ) {
				throw new AutomatonExportException(
						"Unknown mode '" + fromName + "' found as source of transition");
			}

			if( toModeIndex == null ) {
				throw new AutomatonExportException(
						"Unknown mode '" + toName + "' found as destination of transition");
			}

			Tab mode = (Tab)plant.get(fromModeIndex);
			Tab transitionSet;

			if( mode.containsKey("transitions")) {
				transitionSet = (Tab)mode.get("transitions");
			} else {
				transitionSet = new Tab();
				mode.put("transitions", transitionSet);
			}

			String transitionKey = String.format("(%d,%d)", fromModeIndex, toModeIndex);
			Arr transitions;
			if( transitionSet.containsKey(transitionKey)) {
				transitions = (Arr) transitionSet.get(transitionKey);
			} else {
				transitions = new Arr();
				transitionSet.put(transitionKey, transitions);
			}

			Tab transition = new Tab();
			transitions.add(transition);

			Arr guards = new Arr();
			transition.put("guards", guards);

			if (!guard.equals(Constant.TRUE))
			{
				String s = guard.toString();
				String[] gs = s.split("&");

				for (String g : gs) {
					guards.add(g.trim());
				}
			}

			Arr resets = new Arr();
			transition.put("reset", resets);

			for (Entry<String, ExpressionInterval> e : t.reset.entrySet())
			{
				ExpressionInterval ei = e.getValue();
				ei.setExpression(simplifyExpression(ei.getExpression()));

				resets.add((e.getKey() + "\' := " + ei).trim());
			}
		}
	}

	public static class FlowstarExpressionPrinter extends DefaultExpressionPrinter
	{

		public FlowstarExpressionPrinter()
		{
			super();
		}

		@Override
		public String printOperator(Operator op)
		{
			if (op.equals(Operator.GREATER) || op.equals(Operator.LESS)
					|| op.equals(Operator.NOTEQUAL) || op == Operator.OR)
				throw new AutomatonExportException(
						"Flow* printer doesn't support operator '" + op.toDefaultString() + "'");

			return super.printOperator(op);
		}

		@Override
		protected String printTrue()
		{
			return " ";
		}

		@Override
		protected String printFalse()
		{
			return "1 <= 0"; // not really sure if this will work
		}

	}

	@Override
	protected void printAutomaton()
	{
		this.ha = (BaseComponent) config.root;
		flowstarExpressionPrinter = new FlowstarExpressionPrinter();
		Expression.expressionPrinter = flowstarExpressionPrinter;

		printModes();
		printJumps();

		Pickler pickler = new Pickler();
		switch(outputType) {
		case FILE:
			pickler = new Pickler();
			try {
				pickler.dump(plant, outputStream);
			} catch (IOException e) {
				throw new AutomatonExportException("Error pickling", e);
			}
			break;
		case GUI:
			break;
		case NONE:
			break;
		case STDOUT:
			break;
		case STRING:
			pickler = new Pickler();
			try {
				pickler.dump(plant, outputStream);
			} catch (IOException e) {
				throw new AutomatonExportException("Error pickling", e);
			}
			break;
		default:
			break;
		
		
		}
		
		if( outputType == OutputType.FILE ) {
			
		} else {
			printLine(plant.toString(true));
		}
	}

	@Override
	public String getToolName()
	{
		return "Verisig";
	}

	@Override
	public String getCommandLineFlag()
	{
		return "edu/upenn/seas/precise/verisig";
	}

	@Override
	public boolean isInRelease()
	{
		return true;
	}

	@Override
	public String getExtension()
	{
		return ".veri";
	}
}
