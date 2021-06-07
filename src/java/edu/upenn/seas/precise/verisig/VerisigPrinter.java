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
import com.verivital.hyst.ir.network.NetworkComponent;
import com.verivital.hyst.passes.basic.SubstituteConstantsPass;
import com.verivital.hyst.printers.ToolPrinter;
import com.verivital.hyst.util.*;
import org.kohsuke.args4j.Option;

import java.io.IOException;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.util.*;
import java.util.Map.Entry;

/**
 * Printer for Verisig models. Based on Chris' Boogie printer.
 * 
 * @author Taylor Carpenter (2-2019)
 *
 */
public class VerisigPrinter extends ToolPrinter
{
	private static VerisigPrinter INSTANCE;
	public static VerisigPrinter getInstance() {
		return INSTANCE;
	}
	
	@Option(name = "-in-memory", usage = "produce no output")
	boolean inMemory = false;
	
	FlowstarExpressionPrinter flowstarExpressionPrinter;

	private BaseComponent ha;
	public Tab system;
	private Arr states;
	private Tab modes;

	private int modeIndex = 1;
	private HashMap<String, Integer> nameIndexMapping;
	
	private final String DNN_IDENTIFIER = "DNN";

	public VerisigPrinter()
	{
		preconditions = new Preconditions(true);

		system = new Tab();
		states = new Arr();
		modes = new Tab();

		system.put("states", states);
		system.put("modes", modes);

		nameIndexMapping = new HashMap<>();
		
		INSTANCE = this;
	}

	@Override
	protected String getCommentPrefix()
	{
		return "#";
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

	/***
	 * Print variable declarations and their initial value assignments plus a list of all constants
	 */
	private void printVars()
	{
		for (String v : ha.variables)
		{
			states.add(v);
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
			nameIndexMapping.put(locName, modeIndex++);
			
			Tab modeTab = new Tab();
			modes.put(modeIndex-1, modeTab);
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
			modeTab.put("invariant", invariants);
			Expression inv = simplifyExpression(mode.invariant);

			if (!inv.equals(Constant.TRUE))
			{
				invariants.addAll(splitClauses(inv));
			}

			
			Tab transitions = new Tab();
			modeTab.put("transitions", transitions);
		}
		
		/*if(!nameIndexMapping.containsKey(DNN_IDENTIFIER)) {
			throw new AutomatonExportException("No DNN mode found.");
		}*/
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

			Tab mode = (Tab)modes.get(fromModeIndex);
			Tab transitionSet;

			if( mode.containsKey("transitions")) {
				transitionSet = (Tab)mode.get("transitions");
			} else {
				transitionSet = new Tab();
				mode.put("transitions", transitionSet);
			}

			Arr transitions;
			if( transitionSet.containsKey(toModeIndex)) {
				transitions = (Arr) transitionSet.get(toModeIndex);
			} else {
				transitions = new Arr();
				transitionSet.put(toModeIndex, transitions);
			}

			Tab transition = new Tab();
			transitions.add(transition);

			Arr guards = new Arr();
			transition.put("guard", guards);

			Expression g = simplifyExpression(guard);

			if (!g.equals(Constant.TRUE))
			{
				guards.addAll(splitClauses(g));
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
			
			constFormatter = new DecimalFormat("#0.0##############", new DecimalFormatSymbols(Locale.ENGLISH));
			constFormatter.setGroupingUsed(false);
			constFormatter.setMinimumFractionDigits(1);
			constFormatter.setMinimumIntegerDigits(1);
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
	
	protected List<String> splitClauses(Expression expression) {
		List<String> clauses = new ArrayList<>();

		String s = expression.toString();
		int parenCount = 0;
		int lowerBound = 0;
		int upperBound = 0;
		for( ; upperBound < s.length(); upperBound++) {
			switch(s.charAt(upperBound)) {
			case '(':
				parenCount++;
				break;
			case ')':
				parenCount--;
				break;
			case '&':
				if(parenCount == 0) {
					clauses.add(s.substring(lowerBound, upperBound).trim());
					lowerBound = upperBound + 1;
				}
			}
		}
		
		clauses.add(s.substring(lowerBound, upperBound).trim());
		return clauses;
	}

	@Override
	protected void printAutomaton()
	{
		if( config.root instanceof NetworkComponent ) {
			this.ha = (BaseComponent)((NetworkComponent) config.root).children.values().iterator().next().child;
		} else {
			this.ha = (BaseComponent) config.root;
		}
		
		flowstarExpressionPrinter = new FlowstarExpressionPrinter();
		Expression.expressionPrinter = flowstarExpressionPrinter;

		printVars();
		printModes();
		printJumps();
		
		Tab nameMap = new Tab();
		for(Entry<String,Integer> mapping : nameIndexMapping.entrySet()) {
			nameMap.put(mapping.getValue(), mapping.getKey());
		}
		
		system.put("name_map", nameMap);
		

		if(!inMemory) {
			Pickler pickler = new Pickler();
			switch(outputType) {
			case FILE:
				pickler = new Pickler();
				try {
					pickler.dump(system, outputStream);
				} catch (IOException e) {
					throw new AutomatonExportException("Error pickling", e);
				}
				break;
			case STRING:
				pickler = new Pickler();
				try {
					pickler.dump(system, outputStream);
				} catch (IOException e) {
					throw new AutomatonExportException("Error pickling", e);
				}
				break;
			default:
				printLine(system.toString(true));
				break;
			}
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
		return "verisig";
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
