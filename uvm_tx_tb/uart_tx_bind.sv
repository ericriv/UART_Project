bind uart_tx uart_tx_sva #(
	.CLK_FREQ(50_000_000),
	.BAUD_RATE(115200)
) u_sva (
	.clk(clk),
	.rst_(rst_),
	.tx_start(tx_start),
	.tx_data(tx_data),
	.tx_serial(tx_serial),
	.tx_busy(tx_busy)
);