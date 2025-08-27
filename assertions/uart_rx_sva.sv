

module uart_rx_sva #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input 	logic			rst_,
input	logic			rx_serial,
input	logic			rx_data,
input	logic			rx_valid,
input	logic			rx_error
);

localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;



endmodule 