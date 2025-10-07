`include "uvm_macros.svh"
import uvm_pkg::*;

class uart_tx_txn extends uvm_sequence_item;
	logic [7:0] data;

	`uvm_object_utils(uart_tx_txn)

	function new(string name = "uart_tx_txn");
		super.new(name);
	endfunction

	function string convert2string();
		return $sformatf("UART TX data: %0h", data);
	endfunction
endclass
