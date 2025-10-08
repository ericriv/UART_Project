
class uart_tx_driver extends uvm_driver #(uart_tx_txn);
	virtual uart_tx_if vif;

	`uvm_component_utils(uart_tx_driver)
	uvm_analysis_port#(uart_tx_txn) ap;

	function new(string name, uvm_component parent);
		super.new(name, parent);
		ap = new("analysis_port", this);
	endfunction

	function void build_phase(uvm_phase phase);
		if (!uvm_config_db#(virtual uart_tx_if)::get(this, "", "vif", vif))
			`uvm_fatal("NOVIF", "virtual interface not found!")
	endfunction
  
	task reset_phase(uvm_phase phase);
		`uvm_info("DRV", "Waiting for reset deassertion", UVM_LOW)
		wait (vif.rst_ == 1);
		`uvm_info("DRV", "Reset observed, ready for drive", UVM_LOW)
	endtask

	task run_phase(uvm_phase phase);
		uart_tx_txn tr;
		forever begin
			seq_item_port.get_next_item(tr);
			ap.write(tr);
			drive_txn(tr);
			seq_item_port.item_done();
		end
	endtask

	task drive_txn(uart_tx_txn tr);
		vif.cb.tx_data <= tr.data;
		vif.cb.tx_start <= 1;
		@(vif.cb);
		vif.cb.tx_start <= 0;
		@(vif.cb);
		wait (!vif.cb.tx_busy);
	endtask
endclass