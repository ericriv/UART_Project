module uart_rx #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input 	logic			rst_,
input	logic			rx_serial,
output	logic			rx_data,
output	logic			rx_valid,
output	logic			rx_error
);



endmodule