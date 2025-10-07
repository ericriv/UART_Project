
class uart_tx_monitor extends uvm_component;

	`uvm_component_utils(uart_tx_monitor)
	
	uvm_analysis_port#(uart_tx_txn) ap;
	
	virtual uart_tx_if vif;
	int baud_divisor;
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
		ap = new("analysis_port", this);
	endfunction
	
	function void build_phase(uvm_phase phase);
		if (!uvm_config_db#(virtual uart_tx_if)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF", "virtual interface not found!")
		if (!uvm_config_db#(int)::get(this, "", "baud_divisor", baud_divisor))
			`uvm_fatal("MON", "Baud divisor not set")
	endfunction
	
	task run_phase(uvm_phase phase);
		
	endtask
	
	
endclass