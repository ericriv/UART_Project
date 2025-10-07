
class uart_tx_scoreboard extends uvm_component;

	`uvm_component_utils(uart_tx_scoreboard)
	
	uvm_analysis_export#(uart_tx_txn) act_export;
	uvm_analysis_export#(uart_tx_txn) exp_export;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		act_export = new("act_export", this);
		exp_export = new("exp_export", this);
	endfunction
	
	function void write(uart_tx_txn tr);
	
	endfunction
	
	task run_phase(uvm_phase phase);
	
	endtask

endclass