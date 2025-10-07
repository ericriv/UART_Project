
class uart_tx_sequence extends uvm_sequence #(uart_tx_txn);
	`uvm_object_utils(uart_tx_sequence)

	function new(string name = "uart_tx_sequence");
		super.new(name);
	endfunction

	task body();
		repeat (10) begin
		uart_tx_txn tr = uart_tx_txn::type_id::create("tr");
		start_item(tr);
		tr.data  = $urandom_range(0, 255);
		`uvm_info("SEQ", $sformatf("Sending %s", tr.convert2string()), UVM_MEDIUM)
		finish_item(tr);
		end
	endtask
endclass