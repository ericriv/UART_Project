`uvm_analysis_imp_decl(_act)
`uvm_analysis_imp_decl(_exp)

class uart_tx_scoreboard extends uvm_component;

	`uvm_component_utils(uart_tx_scoreboard)
	
	uvm_analysis_imp_act#(uart_tx_txn, uart_tx_scoreboard) act_imp;
	uvm_analysis_imp_exp#(uart_tx_txn, uart_tx_scoreboard) exp_imp;
	uart_tx_txn exp_q[$];
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		act_imp = new("act_imp", this);
		exp_imp = new("exp_imp", this);
	endfunction
	
	function void write_act(uart_tx_txn tr);
		uart_tx_txn exp;
		exp = exp_q.pop_front;
		`uvm_info("SB", $sformatf("Expected %s, Received %s", exp.convert2string(), tr.convert2string()), UVM_MEDIUM)
	endfunction
	
	function void write_exp(uart_tx_txn tr);
		exp_q.push_back(tr);
	endfunction
	
	task run_phase(uvm_phase phase);
	
	endtask

endclass