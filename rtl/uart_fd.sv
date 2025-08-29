module uart_fd #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input	logic			rst_,
input	logic			tx_start,
input	logic	[7:0]	tx_data,
input	logic			rx_serial,
output	logic			tx_serial,
output	logic	[7:0]	rx_data,
output	logic			rx_valid,
output	logic			rx_error,
output	logic			tx_busy
);

	uart_rx #(CLK_FREQ, BAUD_RATE) my_uart_rx(.clk, .rst_, .rx_serial, .rx_data, .rx_valid, .rx_error);
	
	uart_tx #(CLK_FREQ, BAUD_RATE) my_uart_tx(.clk, .rst_,  .tx_start, .tx_data, .tx_serial, .tx_busy);

endmodule 