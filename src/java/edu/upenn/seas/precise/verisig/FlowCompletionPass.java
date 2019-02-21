package edu.upenn.seas.precise.verisig;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import com.verivital.hyst.grammar.formula.Expression;
import com.verivital.hyst.ir.Component;
import com.verivital.hyst.ir.Configuration;
import com.verivital.hyst.ir.base.AutomatonMode;
import com.verivital.hyst.ir.base.BaseComponent;
import com.verivital.hyst.ir.base.ExpressionInterval;
import com.verivital.hyst.ir.network.ComponentInstance;
import com.verivital.hyst.ir.network.NetworkComponent;
import com.verivital.hyst.main.Hyst;
import com.verivital.hyst.passes.TransformationPass;
import com.verivital.hyst.util.Preconditions;

/**
 * A model transformation pass which completes flows by adding flow dynamics
 * for missing states. This pass is a no-op if used without the '-partialflow' flag as
 * the model will have already undergone validation of flow and errored if incomplete
 * 
 * @author Taylor Carpenter (February 2019)
 *
 */
public class FlowCompletionPass extends TransformationPass
{
	public FlowCompletionPass()
	{
		// skip all checks
		preconditions = new Preconditions(true);
	}
	
	@Override
	public String getName()
	{
		return "Complete Flow Dynamics Pass";
	}

	@Override
	public String getCommandLineFlag()
	{
		return "complete_flow";
	}

	@Override
	protected void runPass()
	{
		if (Configuration.DO_FLOW_VALIDATION) {
			return;
		}
		
		completeFlow(config.root);
		
		Configuration.DO_FLOW_VALIDATION = true;
		config.validate();
	}
	
	protected void completeFlow(Component component) {
		if( component instanceof NetworkComponent ) {
			for( ComponentInstance instance : ((NetworkComponent) component).children.values() ) {
				completeFlow(instance.child);
			}
		} else if( component instanceof BaseComponent) {
			BaseComponent ha = (BaseComponent) component;
			
			
			for( String variable : ha.variables ) {
				for( AutomatonMode mode : ha.modes.values() ) {
					if( !mode.flowDynamics.containsKey(variable) ) {
						mode.flowDynamics.put(variable, new ExpressionInterval(0.0));
					}
				}
			}
		}
	}
}
