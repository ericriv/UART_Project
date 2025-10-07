interface uart_tx_if(input bit clk);
	logic rst_;
	logic tx_start;
	logic [7:0] tx_data;
	logic tx_serial;
	logic tx_busy;

	clocking cb @(posedge clk);
		output rst_;
		output tx_start;
		output tx_data;
		input  tx_serial;
		input  tx_busy;
	endclocking
endinterface