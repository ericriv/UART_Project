
class uart_tx_env extends uvm_env;
	uart_tx_driver drv;
	uvm_sequencer #(uart_tx_txn) seqr;
	uart_tx_monitor mon;
	uart_tx_scoreboard sb;

	`uvm_component_utils(uart_tx_env)

	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		drv = uart_tx_driver::type_id::create("drv", this);
		seqr = uvm_sequencer#(uart_tx_txn)::type_id::create("seqr", this);
		mon = uart_tx_monitor::type_id::create("mon", this);
		sb = uart_tx_scoreboard::type_id::create("sb", this);
	endfunction

	function void connect_phase(uvm_phase phase);
		drv.seq_item_port.connect(seqr.seq_item_export);
		mon.ap.connect(sb.act_imp);
		drv.ap.connect(sb.exp_imp);
	endfunction
endclass
