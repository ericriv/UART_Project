`define state_rx uart_fd_tb.my_uart.my_uart_rx.state
`define bit_index_rx uart_fd_tb.my_uart.my_uart_rx.bit_index
`define shifter_rx uart_fd_tb.my_uart.my_uart_rx.shifter
`define sample_tick uart_fd_tb.my_uart.my_uart_rx.sample_tick
`define start_verif_tick uart_fd_tb.my_uart.my_uart_rx.start_verif_tick

`define state_tx uart_fd_tb.my_uart.my_uart_tx.state
`define	baud_cnt uart_fd_tb.my_uart.my_uart_tx.baud_cnt
`define	bit_index_tx uart_fd_tb.my_uart.my_uart_tx.bit_index
`define	shifter_tx uart_fd_tb.my_uart.my_uart_tx.shifter
`define	baud_tick uart_fd_tb.my_uart.my_uart_tx.baud_tick

module uart_fd_sva #(
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

property reset_check;
	@(posedge clk)
		(!rst_ |-> (tx_serial && !tx_busy && `state_tx == uart_fd_tb.my_uart.my_uart_tx.IDLE && `baud_cnt == 0 && `shifter_tx == 0 && `bit_index_tx == 0
			&& rx_data == 0 && `state_rx == uart_fd_tb.my_uart.my_uart_rx.IDLE && !rx_valid && !rx_error && `bit_index_rx == 0 && `shifter_rx == 0));
endproperty
reset_checkP: assert property (reset_check) else $display($stime,"\t\t FAIL::reset_check\n");
reset_checkC: cover property (reset_check) $display($stime,"\t\t PASS::reset_check\n");

//========//
// rx SVA //
//========//

property start_check;
	@(posedge clk) disable iff(!rst_)
		((!rx_serial && `state_rx == uart_fd_tb.my_uart.my_uart_rx.IDLE) |-> ##1 `state_rx == uart_fd_tb.my_uart.my_uart_rx.START);
endproperty
start_checkP: assert property (start_check) else $display($stime,"\t\t FAIL::start_check\n");
start_checkC: cover property (start_check) $display($stime,"\t\t PASS::start_check\n");

property start_verif_check;
	@(posedge clk) disable iff(!rst_)
		((`start_verif_tick && `state_rx == uart_fd_tb.my_uart.my_uart_rx.START && rx_serial) |-> ##1 (`state_rx == uart_fd_tb.my_uart.my_uart_rx.IDLE && rx_error));
endproperty
start_verif_checkP: assert property (start_verif_check) else $display($stime,"\t\t FAIL::start_verif_check\n");
start_verif_checkC: cover property (start_verif_check) $display($stime,"\t\t PASS::start_verif_check\n");

property sample_align_check;
	@(posedge clk) disable iff(!rst_)
		((`state_rx == uart_fd_tb.my_uart.my_uart_rx.DATA && `sample_tick && `bit_index_rx != 3'b111) |-> ##1 `bit_index_rx == ($past(`bit_index_rx)+1));
endproperty
sample_align_checkP: assert property (sample_align_check) else $display($stime,"\t\t FAIL::sample_align_check\n");
sample_align_checkC: cover property (sample_align_check) $display($stime,"\t\t PASS::sample_align_check\n");

property sample_check;
	@(posedge clk) disable iff(!rst_)
		((`state_rx == uart_fd_tb.my_uart.my_uart_rx.DATA && `sample_tick) |-> ##1 `shifter_rx[7] == $past(rx_serial));
endproperty
sample_checkP: assert property (sample_check) else $display($stime,"\t\t FAIL::sample_check\n");
sample_checkC: cover property (sample_check) $display($stime,"\t\t PASS::sample_check\n");

property data_to_stop_check;
	@(posedge clk) disable iff(!rst_)
		((`state_rx == uart_fd_tb.my_uart.my_uart_rx.DATA && `sample_tick && `bit_index_rx == 3'b111) |-> ##1 `state_rx == uart_fd_tb.my_uart.my_uart_rx.STOP);
endproperty
data_to_stop_checkP: assert property (data_to_stop_check) else $display($stime,"\t\t FAIL::data_to_stop_check\n");
data_to_stop_checkC: cover property (data_to_stop_check) $display($stime,"\t\t PASS::data_to_stop_check\n");

property stop_exit_check;
	@(posedge clk) disable iff (!rst_)
		((`state_rx == uart_fd_tb.my_uart.my_uart_rx.STOP && `sample_tick) |-> ##1 (rx_valid ^ rx_error));
endproperty
stop_exit_checkP: assert property (stop_exit_check) else $display($stime,"\t\t FAIL::stop_exit_check\n");
stop_exit_checkC: cover property (stop_exit_check) $display($stime,"\t\t PASS::stop_exit_check\n");

//========//
// tx SVA //
//========//

property idle_high_check;
	@(posedge clk) disable iff(!rst_)
		(!tx_busy |-> tx_serial);
endproperty
idle_high_checkP: assert property (idle_high_check) else $display($stime,"\t\t FAIL::idle_high_check\n");
idle_high_checkC: cover property (idle_high_check) $display($stime,"\t\t PASS::idle_high_check\n");

property start_bit_check;
	@(posedge clk) disable iff(!rst_)
		(`baud_tick && `state_tx == uart_fd_tb.my_uart.my_uart_tx.START |-> !tx_serial);
endproperty
start_bit_checkP: assert property (start_bit_check) else $display($stime,"\t\t FAIL::start_bit_check\n");
start_bit_checkC: cover property (start_bit_check) $display($stime,"\t\t PASS::start_bit_check\n");

property stop_bit_check;
	@(posedge clk) disable iff(!rst_)
		(`baud_tick && `state_tx == uart_fd_tb.my_uart.my_uart_tx.STOP |-> tx_serial);
endproperty
stop_bit_checkP: assert property (stop_bit_check) else $display($stime,"\t\t FAIL::stop_bit_check\n");
stop_bit_checkC: cover property (stop_bit_check) $display($stime,"\t\t PASS::stop_bit_check\n");

property stable_bit_check;
	@(posedge clk) disable iff(!rst_)
		(`baud_tick && tx_busy |-> ##1 $stable(tx_serial) until_with `baud_tick);
endproperty
stable_bit_checkP: assert property (stable_bit_check) else $display($stime, "\t\t FAIL::stable_bit_check\n");
stable_bit_checkC: cover property (stable_bit_check) $display($stime, "\t\t PASS::stable_bit_check\n");

property busy_check;
	@(posedge clk) disable iff(!rst_)
		(tx_start |-> ##1 (tx_busy throughout (`state_tx != uart_fd_tb.my_uart.my_uart_tx.IDLE)));
endproperty
busy_checkP: assert property (busy_check) else $display($stime, "\t\t FAIL::busy_check\n");
busy_checkC: cover property (busy_check) $display($stime, "\t\t PASS::busy_check\n");

property busy_start_check;
	@(posedge clk) disable iff(!rst_)
		(tx_start && tx_busy && !`baud_tick |-> ##1 $stable(`state_tx));
endproperty
busy_start_checkP: assert property (busy_start_check) else $display($stime,"\t\t FAIL::busy_start_check\n");
busy_start_checkC: cover property (busy_start_check) $display($stime,"\t\t PASS::busy_start_check\n");

property no_restart_check;
	@(posedge clk) disable iff(!rst_)
		(tx_start && tx_busy && !`baud_tick |-> ##1 $stable(`shifter_tx));
endproperty
no_restart_checkP: assert property (no_restart_check) else $display($stime,"\t\t FAIL::no_restart_check\n");
no_restart_checkC: cover property (no_restart_check) $display($stime,"\t\t PASS::no_restart_check\n");


endmodule 