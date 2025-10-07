
class uart_tx_test extends uvm_test;
	uart_tx_env env;
	uart_tx_sequence seq;

	`uvm_component_utils(uart_tx_test)

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		env = uart_tx_env::type_id::create("env", this);
	endfunction
  
	task reset_phase(uvm_phase phase);
		phase.raise_objection(this);
		`uvm_info("TEST", "Asserting reset", UVM_LOW)
		env.drv.vif.rst_ <= 0;
		repeat(5) @(env.drv.vif.cb);
		env.drv.vif.rst_ <= 1;
		phase.drop_objection(this);
	endtask

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		wait (env.drv.vif.rst_ == 1);
		@(env.drv.vif.cb);
		seq = uart_tx_sequence::type_id::create("seq");
		seq.start(env.seqr);
		phase.drop_objection(this);
	endtask
endclass