`define state_rx uart_fb_tb.my_uart.my_uart_rx.state
`define bit_index_rx uart_fb_tb.my_uart.my_uart_rx.bit_index
`define shifter_rx uart_fb_tb.my_uart.my_uart_rx.shifter
`define sample_tick uart_fb_tb.my_uart.my_uart_rx.sample_tick
`define start_verif_tick uart_fb_tb.my_uart.my_uart_rx.start_verif_tick

`define state_tx uart_tx_tb.my_uart.my_uart_tx.state
`define	baud_cnt uart_tx_tb.my_uart.my_uart_tx.baud_cnt
`define	bit_index_tx uart_tx_tb.my_uart.my_uart_tx.bit_index
`define	shifter_tx uart_tx_tb.my_uart.my_uart_tx.shifter
`define	baud_tick uart_tx_tb.my_uart.my_uart_tx.baud_tick

module uart_tx_sva #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input	logic			rst_,
input	logic			tx_start,
input	logic	[7:0]	tx_data,
input	logic			tx_serial,
input	logic			tx_busy,
input	logic			rx_serial,
input	logic	[7:0]	rx_data,
input	logic			rx_valid,
input	logic			rx_error
);

