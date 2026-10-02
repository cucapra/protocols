
// Written by Kanna Shimizu

// Copyright by Kanna Shimizu, 2000.  All rights reserved.  This material may
// be freely distributed for educational and research purposes, so long as
// (1) this copyright notice remains, (2) the text is not modified in any
// way, (3) this copyright notice appears in any derived work, (4) no fee is
// charged, and (5) the material is accepted "as-is".  Other uses require the
// written consent of the author.   The copyright holder makes no warranties
// on this document and shall not be liable for any liability or damages.  


// This Verilog file is automatically generated.  The input paramaters are
// 1. The number of agents on the bus.
// 2. The assigned address ranges of each agent.


module PciMonitor (
    frame,
    irdy,
    trdy,
    stop,
    devsel,
    cbe,
    ad,
    frame_e_0,
    frame_o_0,
    irdy_e_0,
    irdy_o_0,
    trdy_e_0,
    trdy_o_0,
    devsel_e_0,
    devsel_o_0,
    stop_e_0,
    stop_o_0,
    cbe_e_0,
    ad_e_0,
    gnt_0,
    req_0,
    idsel_0,
    frame_e_1,
    frame_o_1,
    irdy_e_1,
    irdy_o_1,
    trdy_e_1,
    trdy_o_1,
    devsel_e_1,
    devsel_o_1,
    stop_e_1,
    stop_o_1,
    cbe_e_1,
    ad_e_1,
    gnt_1,
    req_1,
    idsel_1,
    // For Agent 0
    correct0_0,
    correct0_1,
    correct0_2,
    correct0_3,
    correct0_4,
    correct0_5,
    correct0_6,
    correct0_7,
    correct0_8,
    correct0_9,
    correct0_10,
    correct0_11,
    correct0_12,
    correct0_13,
    correct0_14,
    correct0_15,
    correct0_16,
    correct0_17,
    correct0_18,
    correct0_19,
    correct0_20,
    correct0_21,
    correct0_22,
    correct0_23,
    correct0_24,
    correct0_25,
    correct0_26,
    correct0_27,
    correct0_28,
    correct0_29,
    correct0_30,
    correct0_31,
    correct0_32,
    correct0_33,
    correct0_34,
    correct0_35,
    correct0_36,
    correct0_37,
    correct0_38,
    correct0_39,
    correct0_40,
    correct0_41,
    correct0_42,
    correct0_43,
    correct0_44,
    correct0_45,
    correct0_46,
    correct0_47,
    correct0_48,
    correct0_49,
    correct0_50,
    correct0_51,
    correct0_52,
    correct0_53,
    correct0_54,
    correct0_55,
    correct0_56,
    correct0_57,
    correct0_58,
    correct0_59,
    correct0_60,
    correct0_61,
    correct0_62,
    correct0_63,
    correct0_64,
    correct0_65,
    correct0_66,
    correct0_67,
    correct0_68,
    // For Agent 1
    correct1_0,
    correct1_1,
    correct1_2,
    correct1_3,
    correct1_4,
    correct1_5,
    correct1_6,
    correct1_7,
    correct1_8,
    correct1_9,
    correct1_10,
    correct1_11,
    correct1_12,
    correct1_13,
    correct1_14,
    correct1_15,
    correct1_16,
    correct1_17,
    correct1_18,
    correct1_19,
    correct1_20,
    correct1_21,
    correct1_22,
    correct1_23,
    correct1_24,
    correct1_25,
    correct1_26,
    correct1_27,
    correct1_28,
    correct1_29,
    correct1_30,
    correct1_31,
    correct1_32,
    correct1_33,
    correct1_34,
    correct1_35,
    correct1_36,
    correct1_37,
    correct1_38,
    correct1_39,
    correct1_40,
    correct1_41,
    correct1_42,
    correct1_43,
    correct1_44,
    correct1_45,
    correct1_46,
    correct1_47,
    correct1_48,
    correct1_49,
    correct1_50,
    correct1_51,
    correct1_52,
    correct1_53,
    correct1_54,
    correct1_55,
    correct1_56,
    correct1_57,
    correct1_58,
    correct1_59,
    correct1_60,
    correct1_61,
    correct1_62,
    correct1_63,
    correct1_64,
    correct1_65,
    correct1_66,
    correct1_67,
    correct1_68,
    clk
);


  // INPUTS

  // Bus
  input clk;
  input [31:0] ad;
  input frame;
  input irdy;
  input trdy;
  input stop;
  input devsel;
  input [3:0] cbe;
  // Agent 0
  input frame_e_0;
  input frame_o_0;
  input irdy_e_0;
  input irdy_o_0;
  input trdy_e_0;
  input trdy_o_0;
  input devsel_e_0;
  input devsel_o_0;
  input stop_e_0;
  input stop_o_0;
  input cbe_e_0;
  input ad_e_0;
  input gnt_0;
  input req_0;
  input idsel_0;
  // Agent 1
  input frame_e_1;
  input frame_o_1;
  input irdy_e_1;
  input irdy_o_1;
  input trdy_e_1;
  input trdy_o_1;
  input devsel_e_1;
  input devsel_o_1;
  input stop_e_1;
  input stop_o_1;
  input cbe_e_1;
  input ad_e_1;
  input gnt_1;
  input req_1;
  input idsel_1;


  // OUTPUTS : The output declarations.

  // Correct Variables.
  // For Agent 0
  output correct0_0;
  output correct0_1;
  output correct0_2;
  output correct0_3;
  output correct0_4;
  output correct0_5;
  output correct0_6;
  output correct0_7;
  output correct0_8;
  output correct0_9;
  output correct0_10;
  output correct0_11;
  output correct0_12;
  output correct0_13;
  output correct0_14;
  output correct0_15;
  output correct0_16;
  output correct0_17;
  output correct0_18;
  output correct0_19;
  output correct0_20;
  output correct0_21;
  output correct0_22;
  output correct0_23;
  output correct0_24;
  output correct0_25;
  output correct0_26;
  output correct0_27;
  output correct0_28;
  output correct0_29;
  output correct0_30;
  output correct0_31;
  output correct0_32;
  output correct0_33;
  output correct0_34;
  output correct0_35;
  output correct0_36;
  output correct0_37;
  output correct0_38;
  output correct0_39;
  output correct0_40;
  output correct0_41;
  output correct0_42;
  output correct0_43;
  output correct0_44;
  output correct0_45;
  output correct0_46;
  output correct0_47;
  output correct0_48;
  output correct0_49;
  output correct0_50;
  output correct0_51;
  output correct0_52;
  output correct0_53;
  output correct0_54;
  output correct0_55;
  output correct0_56;
  output correct0_57;
  output correct0_58;
  output correct0_59;
  output correct0_60;
  output correct0_61;
  output correct0_62;
  output correct0_63;
  output correct0_64;
  output correct0_65;
  output correct0_66;
  output correct0_67;
  output correct0_68;
  // For Agent 1
  output correct1_0;
  output correct1_1;
  output correct1_2;
  output correct1_3;
  output correct1_4;
  output correct1_5;
  output correct1_6;
  output correct1_7;
  output correct1_8;
  output correct1_9;
  output correct1_10;
  output correct1_11;
  output correct1_12;
  output correct1_13;
  output correct1_14;
  output correct1_15;
  output correct1_16;
  output correct1_17;
  output correct1_18;
  output correct1_19;
  output correct1_20;
  output correct1_21;
  output correct1_22;
  output correct1_23;
  output correct1_24;
  output correct1_25;
  output correct1_26;
  output correct1_27;
  output correct1_28;
  output correct1_29;
  output correct1_30;
  output correct1_31;
  output correct1_32;
  output correct1_33;
  output correct1_34;
  output correct1_35;
  output correct1_36;
  output correct1_37;
  output correct1_38;
  output correct1_39;
  output correct1_40;
  output correct1_41;
  output correct1_42;
  output correct1_43;
  output correct1_44;
  output correct1_45;
  output correct1_46;
  output correct1_47;
  output correct1_48;
  output correct1_49;
  output correct1_50;
  output correct1_51;
  output correct1_52;
  output correct1_53;
  output correct1_54;
  output correct1_55;
  output correct1_56;
  output correct1_57;
  output correct1_58;
  output correct1_59;
  output correct1_60;
  output correct1_61;
  output correct1_62;
  output correct1_63;
  output correct1_64;
  output correct1_65;
  output correct1_66;
  output correct1_67;
  output correct1_68;


  // Reg/Wire declarations

  // Declaration for prev and double prev variables for all agents 
  reg p_gnt_1;
  reg p_frame_o_1;
  reg p_irdy_o_1;
  reg p_t_sel_1;
  reg p_idsel_1;
  reg p_devsel_o_1;
  reg p_trdy_o_1;
  reg p_stop_o_1;
  reg p_req_1;
  reg p_req_0;
  reg p_initial_data_phase;
  reg [4:0] p_m_initial;
  reg [4:0] p_m_subseq;
  reg [4:0] p_m_irdy_timeout;
  reg p_timeout;
  reg p_devsel_history;
  reg p_read_command;
  reg p_in_addr_phase;
  reg p_dphase_done;
  reg p_irdy;
  reg p_target_abort;
  reg [4:0] p_t_initial;
  reg [4:0] p_t_subseq;
  reg p_stop;
  reg p_trdy;
  reg p_devsel;
  reg [4:0] p_frame_7;
  reg p_in_write_tran;
  reg p_gnt_0;
  reg p_frame_o_0;
  reg p_irdy_o_0;
  reg p_frame_e_1;
  reg p_frame_e_0;
  reg p_irdy_e_1;
  reg p_irdy_e_0;
  reg p_idle;
  reg p_final_dphase_done;
  reg p_in_read_tran;
  reg p_frame;
  reg p_t_sel_0;
  reg p_idsel_0;
  reg p_devsel_o_0;
  reg p_trdy_o_0;
  reg p_stop_o_0;
  reg p_devsel_e_1;
  reg p_devsel_e_0;
  reg p_trdy_e_1;
  reg p_trdy_e_0;
  reg p_stop_e_1;
  reg p_stop_e_0;
  reg pp_gnt_1;
  reg pp_stop;
  reg pp_gnt_0;
  reg pp_frame;

  // Correct variables.
  // For Agent 0
  reg correct0_0;
  reg correct0_1;
  reg correct0_2;
  reg correct0_3;
  reg correct0_4;
  reg correct0_5;
  reg correct0_6;
  reg correct0_7;
  reg correct0_8;
  reg correct0_9;
  reg correct0_10;
  reg correct0_11;
  reg correct0_12;
  reg correct0_13;
  reg correct0_14;
  reg correct0_15;
  reg correct0_16;
  reg correct0_17;
  reg correct0_18;
  reg correct0_19;
  reg correct0_20;
  reg correct0_21;
  reg correct0_22;
  reg correct0_23;
  reg correct0_24;
  reg correct0_25;
  reg correct0_26;
  reg correct0_27;
  reg correct0_28;
  reg correct0_29;
  reg correct0_30;
  reg correct0_31;
  reg correct0_32;
  reg correct0_33;
  reg correct0_34;
  reg correct0_35;
  reg correct0_36;
  reg correct0_37;
  reg correct0_38;
  reg correct0_39;
  reg correct0_40;
  reg correct0_41;
  reg correct0_42;
  reg correct0_43;
  reg correct0_44;
  reg correct0_45;
  reg correct0_46;
  reg correct0_47;
  reg correct0_48;
  reg correct0_49;
  reg correct0_50;
  reg correct0_51;
  reg correct0_52;
  reg correct0_53;
  reg correct0_54;
  reg correct0_55;
  reg correct0_56;
  reg correct0_57;
  reg correct0_58;
  reg correct0_59;
  reg correct0_60;
  reg correct0_61;
  reg correct0_62;
  reg correct0_63;
  reg correct0_64;
  reg correct0_65;
  reg correct0_66;
  reg correct0_67;
  reg correct0_68;
  // For Agent 1
  reg correct1_0;
  reg correct1_1;
  reg correct1_2;
  reg correct1_3;
  reg correct1_4;
  reg correct1_5;
  reg correct1_6;
  reg correct1_7;
  reg correct1_8;
  reg correct1_9;
  reg correct1_10;
  reg correct1_11;
  reg correct1_12;
  reg correct1_13;
  reg correct1_14;
  reg correct1_15;
  reg correct1_16;
  reg correct1_17;
  reg correct1_18;
  reg correct1_19;
  reg correct1_20;
  reg correct1_21;
  reg correct1_22;
  reg correct1_23;
  reg correct1_24;
  reg correct1_25;
  reg correct1_26;
  reg correct1_27;
  reg correct1_28;
  reg correct1_29;
  reg correct1_30;
  reg correct1_31;
  reg correct1_32;
  reg correct1_33;
  reg correct1_34;
  reg correct1_35;
  reg correct1_36;
  reg correct1_37;
  reg correct1_38;
  reg correct1_39;
  reg correct1_40;
  reg correct1_41;
  reg correct1_42;
  reg correct1_43;
  reg correct1_44;
  reg correct1_45;
  reg correct1_46;
  reg correct1_47;
  reg correct1_48;
  reg correct1_49;
  reg correct1_50;
  reg correct1_51;
  reg correct1_52;
  reg correct1_53;
  reg correct1_54;
  reg correct1_55;
  reg correct1_56;
  reg correct1_57;
  reg correct1_58;
  reg correct1_59;
  reg correct1_60;
  reg correct1_61;
  reg correct1_62;
  reg correct1_63;
  reg correct1_64;
  reg correct1_65;
  reg correct1_66;
  reg correct1_67;
  reg correct1_68;

  // The masteris variables are declared.
  reg masteris_0;
  reg masteris_1;
  // The targetis variables are declared.
  reg targetis_0;
  reg targetis_1;

  // Misc. wire/reg declarations

  wire in_addr_phase;
  wire idle;
  wire m_term;
  wire dphase_done;
  wire data_transfer;
  wire target_abort;
  wire final_dphase_done;
  wire retry;
  wire disconnect_wdata;
  wire disconnect_woutdata;
  wire b2b;
  wire m_abort_cond;
  wire master_abort;
  wire timeout;
  wire read_command;
  wire write_command;
  wire is_cbe_com;

  wire initial_data_phase;
  wire devsel_history;
  wire m_abort;
  wire in_read_tran;
  wire in_write_tran;

  wire [4:0] frame_32;
  wire [4:0] frame_7;
  wire [4:0] t_initial;
  wire [4:0] t_subseq;
  wire [4:0] m_initial;
  wire [4:0] m_subseq;
  wire [4:0] m_irdy_timeout;

  wire [4:0] thirty_one;
  wire [4:0] seven;
  wire [4:0] five;
  wire [4:0] seventeen;
  wire [4:0] nine;
  wire [4:0] three;

  wire t_sel_0;
  wire t_sel_1;
  // Assigns for macros.

  assign in_addr_phase = (!p_frame && frame);

  assign idle = !frame && !irdy;

  assign m_term = !frame && irdy;

  assign dphase_done = irdy && (trdy || stop);
  assign final_dphase_done = irdy && (trdy || stop) && !frame;

  assign data_transfer = trdy && irdy;

  assign target_abort = !devsel && stop && !trdy;
  assign retry = !trdy && stop && initial_data_phase;
  assign disconnect_wdata = trdy && stop && devsel;
  assign disconnect_woutdata = !trdy && stop && devsel && !initial_data_phase;

  // There is a back-to-back iff frame becomes asserted right
  // after the final data phase.  (Otherwise, there will be an idle because
  // irdy is required to be deasserted the clock after final dphase done.)


  assign b2b = !p_frame && frame && p_final_dphase_done;

  // This is needed because of the delay in state machines.  Namely, m_abort
  // can only become true a cycle after the occurence of m_abort but this
  // variable turns true in the same cycle as when a master abort happens.
  assign m_abort_cond = ((p_frame && !frame) && p_irdy && !(p_stop || p_trdy)) 
             || ((p_irdy && !irdy) && !p_frame && !(p_stop || p_trdy));

  // defined so as to check for a master abort event.
  assign master_abort = m_abort_cond || m_abort;

  // The timeout is set as this for now.
  assign timeout = (frame_32 == 5'b11111);

  // Read and write are defined
  assign read_command = 
((cbe == 4'b0110) || (cbe == 4'b0010) || (cbe == 4'b1100) || (cbe == 4'b1110)
|| (cbe == 4'b1010));

  assign write_command = 
 ((cbe == 4'b0111) || (cbe == 4'b0011) || (cbe == 4'b1011) || (cbe == 4'b1111));

  assign is_cbe_com = ((cbe == 4'b1010) || (cbe == 4'b1011));


  assign t_sel_0 = ((32'h00000000 <= ad) && (ad < 32'h00000000)) ? 1'b1 : 1'b0;
  assign t_sel_1 = ((32'h00000000 <= ad) && (ad < 32'h00000000)) ? 1'b1 : 1'b0;



  // Module State Machines

  // History Modules

  // Have to record the fact that a master abort has happened.  
  history m_abort_h (
      m_abort_cond && !idle && !in_addr_phase,
      idle || in_addr_phase,
      m_abort
  );

  // In a read transaction.  It is incorrect for the addr_phase and the first
  // phase of idle after master abort.
  history in_read_tran_h (
      in_addr_phase && read_command,
      in_addr_phase & write_command || idle || final_dphase_done,
      in_read_tran
  );

  // In a write transaction.  It is incorrect for the addr_phase and the first
  // phase of idle after master abort.
  history in_write_tran_h (
      in_addr_phase && write_command,
      in_addr_phase & read_command || idle || final_dphase_done,
      in_write_tran
  );

  // This has a slight delay but since it's only used for retry and
  // disconnect_woutdata where a master abort doesn't happen and dphase_done
  // does become true, not to worry.
  history initial_data_phase_h (
      in_addr_phase,
      dphase_done || idle,
      initial_data_phase
  );

  // final_dphase_complete must happen because a master abort cannot have
  // happened if devsel_history is true.
  history devsel_history_h (
      !p_devsel && devsel && !final_dphase_done,
      final_dphase_done,
      devsel_history
  );

  // Counter Modules

  assign thirty_one = 5'b11111;
  assign seven = 5'b00111;
  assign five = 5'b00101;
  assign seventeen = 5'b10001;
  assign nine = 5'b01001;
  assign three = 5'b00011;

  counter frame_32_c (
      clk,
      !p_frame && frame,
      !frame,
      frame_32,
      thirty_one
  );

  counter frame_7_c (
      clk,
      !p_frame && frame,
      idle || final_dphase_done,
      frame_7,
      seven
  );

  counter t_initial_c (
      clk,
      !p_frame && frame,
      trdy || stop || (frame_7 == five) & !devsel_history,
      t_initial,
      seventeen
  );

  counter t_subseq_c (
      clk,
      irdy && (trdy || stop) && frame,
      trdy || stop,
      t_subseq,
      nine
  );

  counter m_initial_c (
      clk,
      !p_frame && frame,
      irdy,
      m_initial,
      nine
  );

  counter m_subseq_c (
      clk,
      irdy && (trdy || stop) && frame,
      irdy,
      m_subseq,
      nine
  );

  // termination can be delayed if IRDY# is deasserted because FRAME# cannot be
  // deasserted until IRDY# is asserted.  "This delay in termination should not
  // be extended more than two or three clocks." after GNT# has been
  // deasserted.  (3.3.3.1 p39) (internal counter)

  counter m_irdy_timeout_c (
      clk,
      !p_timeout && timeout && ((masteris_0 && gnt_0) || (masteris_1 && !gnt_1)) && !irdy,
      irdy,
      m_irdy_timeout,
      three
  );








  // INITIALIZATIONS 

  initial begin

    // Initializing the correct variables.

    // For Agent 0
    correct0_0 = 1'b1;
    correct0_1 = 1'b1;
    correct0_2 = 1'b1;
    correct0_3 = 1'b1;
    correct0_4 = 1'b1;
    correct0_5 = 1'b1;
    correct0_6 = 1'b1;
    correct0_7 = 1'b1;
    correct0_8 = 1'b1;
    correct0_9 = 1'b1;
    correct0_10 = 1'b1;
    correct0_11 = 1'b1;
    correct0_12 = 1'b1;
    correct0_13 = 1'b1;
    correct0_14 = 1'b1;
    correct0_15 = 1'b1;
    correct0_16 = 1'b1;
    correct0_17 = 1'b1;
    correct0_18 = 1'b1;
    correct0_19 = 1'b1;
    correct0_20 = 1'b1;
    correct0_21 = 1'b1;
    correct0_22 = 1'b1;
    correct0_23 = 1'b1;
    correct0_24 = 1'b1;
    correct0_25 = 1'b1;
    correct0_26 = 1'b1;
    correct0_27 = 1'b1;
    correct0_28 = 1'b1;
    correct0_29 = 1'b1;
    correct0_30 = 1'b1;
    correct0_31 = 1'b1;
    correct0_32 = 1'b1;
    correct0_33 = 1'b1;
    correct0_34 = 1'b1;
    correct0_35 = 1'b1;
    correct0_36 = 1'b1;
    correct0_37 = 1'b1;
    correct0_38 = 1'b1;
    correct0_39 = 1'b1;
    correct0_40 = 1'b1;
    correct0_41 = 1'b1;
    correct0_42 = 1'b1;
    correct0_43 = 1'b1;
    correct0_44 = 1'b1;
    correct0_45 = 1'b1;
    correct0_46 = 1'b1;
    correct0_47 = 1'b1;
    correct0_48 = 1'b1;
    correct0_49 = 1'b1;
    correct0_50 = 1'b1;
    correct0_51 = 1'b1;
    correct0_52 = 1'b1;
    correct0_53 = 1'b1;
    correct0_54 = 1'b1;
    correct0_55 = 1'b1;
    correct0_56 = 1'b1;
    correct0_57 = 1'b1;
    correct0_58 = 1'b1;
    correct0_59 = 1'b1;
    correct0_60 = 1'b1;
    correct0_61 = 1'b1;
    correct0_62 = 1'b1;
    correct0_63 = 1'b1;
    correct0_64 = 1'b1;
    correct0_65 = 1'b1;
    correct0_66 = 1'b1;
    correct0_67 = 1'b1;
    correct0_68 = 1'b1;
    // For Agent 1
    correct1_0 = 1'b1;
    correct1_1 = 1'b1;
    correct1_2 = 1'b1;
    correct1_3 = 1'b1;
    correct1_4 = 1'b1;
    correct1_5 = 1'b1;
    correct1_6 = 1'b1;
    correct1_7 = 1'b1;
    correct1_8 = 1'b1;
    correct1_9 = 1'b1;
    correct1_10 = 1'b1;
    correct1_11 = 1'b1;
    correct1_12 = 1'b1;
    correct1_13 = 1'b1;
    correct1_14 = 1'b1;
    correct1_15 = 1'b1;
    correct1_16 = 1'b1;
    correct1_17 = 1'b1;
    correct1_18 = 1'b1;
    correct1_19 = 1'b1;
    correct1_20 = 1'b1;
    correct1_21 = 1'b1;
    correct1_22 = 1'b1;
    correct1_23 = 1'b1;
    correct1_24 = 1'b1;
    correct1_25 = 1'b1;
    correct1_26 = 1'b1;
    correct1_27 = 1'b1;
    correct1_28 = 1'b1;
    correct1_29 = 1'b1;
    correct1_30 = 1'b1;
    correct1_31 = 1'b1;
    correct1_32 = 1'b1;
    correct1_33 = 1'b1;
    correct1_34 = 1'b1;
    correct1_35 = 1'b1;
    correct1_36 = 1'b1;
    correct1_37 = 1'b1;
    correct1_38 = 1'b1;
    correct1_39 = 1'b1;
    correct1_40 = 1'b1;
    correct1_41 = 1'b1;
    correct1_42 = 1'b1;
    correct1_43 = 1'b1;
    correct1_44 = 1'b1;
    correct1_45 = 1'b1;
    correct1_46 = 1'b1;
    correct1_47 = 1'b1;
    correct1_48 = 1'b1;
    correct1_49 = 1'b1;
    correct1_50 = 1'b1;
    correct1_51 = 1'b1;
    correct1_52 = 1'b1;
    correct1_53 = 1'b1;
    correct1_54 = 1'b1;
    correct1_55 = 1'b1;
    correct1_56 = 1'b1;
    correct1_57 = 1'b1;
    correct1_58 = 1'b1;
    correct1_59 = 1'b1;
    correct1_60 = 1'b1;
    correct1_61 = 1'b1;
    correct1_62 = 1'b1;
    correct1_63 = 1'b1;
    correct1_64 = 1'b1;
    correct1_65 = 1'b1;
    correct1_66 = 1'b1;
    correct1_67 = 1'b1;
    correct1_68 = 1'b1;


    // The masteris variables are initialized.
    masteris_0 = 1'b0;
    masteris_1 = 1'b0;

    // The targetis variables are initialized.
    targetis_0 = 1'b0;
    targetis_1 = 1'b0;

    // Initializations for p_ and pp_ vars.

    p_gnt_1 = 1'b0;
    p_frame_o_1 = 1'b0;
    p_irdy_o_1 = 1'b0;
    p_t_sel_1 = 1'b0;
    p_idsel_1 = 1'b0;
    p_devsel_o_1 = 1'b0;
    p_trdy_o_1 = 1'b0;
    p_stop_o_1 = 1'b0;
    p_req_1 = 1'b0;
    p_req_0 = 1'b0;
    p_initial_data_phase <= 1'b0;
    p_m_initial <= 5'b00000;
    p_m_subseq <= 5'b00000;
    p_m_irdy_timeout <= 5'b00000;
    p_timeout <= 1'b0;
    p_devsel_history <= 1'b0;
    p_read_command <= 1'b0;
    p_in_addr_phase <= 1'b0;
    p_dphase_done <= 1'b0;
    p_irdy <= 1'b0;
    p_target_abort <= 1'b0;
    p_t_initial <= 5'b00000;
    p_t_subseq <= 5'b00000;
    p_stop <= 1'b0;
    p_trdy <= 1'b0;
    p_devsel <= 1'b0;
    p_frame_7 <= 5'b00000;
    p_in_write_tran <= 1'b0;
    p_gnt_0 = 1'b0;
    p_frame_o_0 = 1'b0;
    p_irdy_o_0 = 1'b0;
    p_frame_e_1 = 1'b0;
    p_frame_e_0 = 1'b0;
    p_irdy_e_1 = 1'b0;
    p_irdy_e_0 = 1'b0;
    p_idle <= 1'b0;
    p_final_dphase_done <= 1'b0;
    p_in_read_tran <= 1'b0;
    p_frame <= 1'b0;
    p_t_sel_0 = 1'b0;
    p_idsel_0 = 1'b0;
    p_devsel_o_0 = 1'b0;
    p_trdy_o_0 = 1'b0;
    p_stop_o_0 = 1'b0;
    p_devsel_e_1 = 1'b0;
    p_devsel_e_0 = 1'b0;
    p_trdy_e_1 = 1'b0;
    p_trdy_e_0 = 1'b0;
    p_stop_e_1 = 1'b0;
    p_stop_e_0 = 1'b0;
    pp_gnt_1 = 1'b0;
    pp_stop <= 1'b0;
    pp_gnt_0 = 1'b0;
    pp_frame <= 1'b0;

  end  // END INITIALIZATION




  // BEGIN MAJOR BLOCK


  always @(posedge clk) begin


    // The constraints for all agents

    // For agent 0

    if (correct0_0 && (gnt_0) && !(!gnt_1)) correct0_0 <= 1'b0;
    else correct0_0 <= correct0_0;

    /* if in idle, there must be a one clock delay between deasserting one gnt
  and asserting another gnt.  This is because of address stepping. */

    if (correct0_1 && (p_idle && p_gnt_0) && !((gnt_0 || !gnt_1 && !gnt_0))) correct0_1 <= 1'b0;
    else correct0_1 <= correct0_1;

    /* if gnt is given to something that didn't request it, it must be because
     of arbitration parking where no agents are requesting the bus.*/

    if (correct0_2 && (!p_gnt_0 && !p_req_0 && (p_req_1 || p_req_0)) && !(!gnt_0))
      correct0_2 <= 1'b0;
    else correct0_2 <= correct0_2;

    /* the cbe buffers must remain enabled from the first clock of the data
 phase through the end of the transaction.  */

    if (correct0_3 && (masteris_0 && !p_final_dphase_done && !p_idle) && !(cbe_e_0))
      correct0_3 <= 1'b0;
    else correct0_3 <= correct0_3;

    /* during a write cycle, whenever irdy is asserted, then the bus is driven by
 master.  The "!in_addr_phase" is needed because the master_is value and
 in_write_tran value are not valid during the address phase.*/

    if (correct0_4 && (masteris_0  && irdy_e_0 && irdy_o_0 && in_write_tran &&
!in_addr_phase) && !(ad_e_0))
      correct0_4 <= 1'b0;
    else correct0_4 <= correct0_4;

    /* only when IRDY is asserted can FRAME be deasserted.*/

    if (correct0_5 && (masteris_0  && p_frame) && !((frame_e_0 && frame_o_0 ||
irdy_e_0 && irdy_o_0)))
      correct0_5 <= 1'b0;
    else correct0_5 <= correct0_5;

    /* if frame does deassert and irdy wasn't asserted on the same clock *and* a
 data phase hasn't just completed, the following master abort conditions
 must hold.  (frame changing by deasserting)*/

    if (correct0_6 && (masteris_0  && !((p_stop || p_trdy)) && p_frame && p_irdy
&& (((p_devsel || p_devsel_history) || !p_initial_data_phase) ||
!(p_frame_7 >= 4))) && !(frame_e_0 && frame_o_0))
      correct0_6 <= 1'b0;
    else correct0_6 <= correct0_6;

    /* once irdy is asserted, it can only deassert without a dphase done, if a
 master abort has happened.  We must consider the case where the
 transaction attempted was a one data phase one.*/

    if (correct0_7 && (masteris_0  && p_irdy && !((p_stop || p_trdy)) &&
(((p_devsel || p_devsel_history) || !p_initial_data_phase) ||
!(p_frame_7 >= 4))) && !((irdy_e_0 && irdy_o_0 || m_abort)))
      correct0_7 <= 1'b0;
    else correct0_7 <= correct0_7;

    /* master must raise irdy within 8 cycles of the assertion of frame.*/

    if (correct0_8 && (masteris_0 && p_m_initial == 7 && !p_irdy) && !(irdy_e_0 && irdy_o_0))
      correct0_8 <= 1'b0;
    else correct0_8 <= correct0_8;

    /* master must raise irdy within 8 cycles of the last data completion.*/

    if (correct0_9 && (masteris_0 && p_m_subseq == 7 && !p_irdy) && !(irdy_e_0 && irdy_o_0))
      correct0_9 <= 1'b0;
    else correct0_9 <= correct0_9;

    /* For a timeout situation, the master must not delay the assertion of irdy.
 termination can be delayed if IRDY# is deasserted because FRAME# cannot be
 deasserted until IRDY# is asserted.  "This delay in termination should not
 be extended more than two or three clocks." after GNT# has been
 deasserted.  (3.3.3.1 p39) (internal counter)*/

    if (correct0_10 && (masteris_0 && p_m_irdy_timeout == 3 && !p_irdy) && !(irdy_e_0 && irdy_o_0))
      correct0_10 <= 1'b0;
    else correct0_10 <= correct0_10;

    /* once irdy is asserted, frame can never change from deasserted to asserted
 until the data phase completes.*/

    if (correct0_11 && (masteris_0  && p_irdy && !p_frame &&
!p_dphase_done) && !((!frame_e_0 || !frame_o_0 && frame_e_0)))
      correct0_11 <= 1'b0;
    else correct0_11 <= correct0_11;

    /* if gnt is deasserted before the natural completion of the transaction and
 there is a timeout, continued use of the bus is not allowed.
 1. If a data phase has just completed, the next data phase cannot be a non
 m_term one.
 2. If irdy is deasserted, the next data phase cannot be a non m_term one.
 3. If frame and irdy are both asserted and a master abort is allowed to
 happen, the master must master abort.*/

    if (correct0_12 && (masteris_0  && p_timeout && !p_gnt_0 && p_dphase_done &&
p_frame && p_irdy) && !(!(frame_e_0 && frame_o_0 && irdy_e_0 && irdy_o_0)))
      correct0_12 <= 1'b0;
    else correct0_12 <= correct0_12;

    if (correct0_13 && (masteris_0  && p_timeout && !p_gnt_0 && p_frame &&
!p_irdy) && !(!(frame_e_0 && frame_o_0 && irdy_e_0 && irdy_o_0)))
      correct0_13 <= 1'b0;
    else correct0_13 <= correct0_13;

    if (correct0_14 && (masteris_0  && p_timeout && !p_gnt_0 && p_frame && p_irdy
&& !p_devsel && !p_devsel_history) && !((!frame_e_0 || !frame_o_0 &&
frame_e_0)))
      correct0_14 <= 1'b0;
    else correct0_14 <= correct0_14;

    /* Whenever stop is asserted, the master must deassert frame as soon as irdy
 is asserted.*/

    if (correct0_15 && (masteris_0  && p_stop && !p_irdy) && !(!(frame_e_0 &&
frame_o_0 && irdy_e_0 && irdy_o_0)))
      correct0_15 <= 1'b0;
    else correct0_15 <= correct0_15;

    if (correct0_16 && (masteris_0  && p_stop && p_irdy &&
p_dphase_done) && !(!(frame_e_0 && frame_o_0 && irdy_e_0 && irdy_o_0)))
      correct0_16 <= 1'b0;
    else correct0_16 <= correct0_16;

    /* irdy must be deasserted the clock following the completion of the last data
 phase.*/

    if (correct0_17 && (masteris_0  && p_final_dphase_done) && !((!irdy_e_0 ||
!irdy_o_0 && irdy_e_0)))
      correct0_17 <= 1'b0;
    else correct0_17 <= correct0_17;

    /* if a stop had happened, req must be deasserted on the clock the bus
 becomes idle and also either the clock before or clocks after.  */

    if (correct0_18 && (masteris_0  && p_devsel && pp_stop && p_stop &&
p_final_dphase_done) && !(!req_0))
      correct0_18 <= 1'b0;
    else correct0_18 <= correct0_18;

    /* scenario a : there must be an idle after a transaction terminated by a
 retry or disconnect.  This is hard to assign blame so break it up.*/

    if (correct0_19 && (masteris_0  && p_devsel && pp_stop && p_stop &&
p_final_dphase_done) && !((!frame_e_0 || !frame_o_0 && frame_e_0) &&
(!irdy_e_0 || !irdy_o_0 && irdy_e_0)))
      correct0_19 <= 1'b0;
    else correct0_19 <= correct0_19;

    /* cbes must be enabled during the address phase to issue the trans
   command.*/

    if (correct0_20 && (!p_frame) && !((!(frame_e_0 && frame_o_0) || cbe_e_0))) correct0_20 <= 1'b0;
    else correct0_20 <= correct0_20;

    /* during the address phase, AD is driven by the master.*/

    if (correct0_21 && (!p_frame) && !((!(frame_e_0 && frame_o_0) || ad_e_0))) correct0_21 <= 1'b0;
    else correct0_21 <= correct0_21;

    /* a turnaround cycle is required for a read.  (Required for both the
   target and the master.)*/

    if (correct0_22 && (p_in_addr_phase && p_read_command) && !(!ad_e_0)) correct0_22 <= 1'b0;
    else correct0_22 <= correct0_22;

    /* ad and cbe use the idle state as their turnaround cycle.*/

    if (correct0_23 && (!in_read_tran && !irdy_e_0 && !frame_e_0) && !(!cbe_e_0 && !ad_e_0))
      correct0_23 <= 1'b0;
    else correct0_23 <= correct0_23;

    /* the addr phase is a turnaround cycle for irdy when the transaction is not
   a b2b.*/

    if (correct0_24 && (p_idle) && !(!irdy_e_0)) correct0_24 <= 1'b0;
    else correct0_24 <= correct0_24;

    /* cannot be both a read command and a write command.  This is not really a
   PCI spec but is a fact and is needed for verifying this spec.*/

    if (correct0_25 && (!p_frame) && !((!(frame_e_0 && frame_o_0) ||
!(read_command && write_command))))
      correct0_25 <= 1'b0;
    else correct0_25 <= correct0_25;

    /* it is either a write command or a read command.
   This is not really a PCI spec but is a fact and is needed for verifying
   this spec.*/

    if (correct0_26 && (!p_frame) && !((!(frame_e_0 && frame_o_0) ||
(read_command || write_command))))
      correct0_26 <= 1'b0;
    else correct0_26 <= correct0_26;

    /* can only start a transaction if gnt is high.  Cover b2b case.*/

    if (correct0_27 && (!p_frame && !p_gnt_0) && !(!(frame_e_0 && frame_o_0))) correct0_27 <= 1'b0;
    else correct0_27 <= correct0_27;

    /*frame & !idle & !final_dphase_done -> next(!assert(i, frame));*/

    if (correct0_28 && (!p_frame && p_irdy && !((p_trdy ||
p_stop))) && !(!(frame_e_0 && frame_o_0)))
      correct0_28 <= 1'b0;
    else correct0_28 <= correct0_28;

    /* turnaround cycle enforced by a deasserted trdy.  In this phase, it can be
 driven deasserted, or floated deasserted.*/

    if (correct0_29 && (targetis_0  && p_read_command &&
p_in_addr_phase) && !((!trdy_e_0 || !trdy_o_0 && trdy_e_0)))
      correct0_29 <= 1'b0;
    else correct0_29 <= correct0_29;

    /* target can only assert trdy if devsel is asserted.  This also stipulates
 that an agent can only assert trdy if it had claimed the transaction by
 asserting devsel.  */

    if (correct0_30 && (targetis_0 && trdy_e_0 && trdy_o_0) && !(devsel_e_0 && devsel_o_0))
      correct0_30 <= 1'b0;
    else correct0_30 <= correct0_30;

    /* Once stop is asserted, it must remain asserted until frame is
 deasserted.  */

    if (correct0_31 && (targetis_0 && p_stop && p_frame) && !(stop_e_0 && stop_o_0))
      correct0_31 <= 1'b0;
    else correct0_31 <= correct0_31;

    /* Once frame is deasserted, stop must be deasserted.  */

    if (correct0_32 && (targetis_0  && pp_frame && !p_frame) && !((!stop_e_0 ||
!stop_o_0 && stop_e_0)))
      correct0_32 <= 1'b0;
    else correct0_32 <= correct0_32;

    /* Once target has asserted trdy, it cannot change devsel, trdy, or stop
 until the data phase compeltes.  (devsel rule already implied by rest.)*/

    if (correct0_33 && (targetis_0 && p_trdy && !p_dphase_done) && !(trdy_e_0 && trdy_o_0))
      correct0_33 <= 1'b0;
    else correct0_33 <= correct0_33;

    if (correct0_34 && (targetis_0  && p_trdy && p_stop &&
!p_dphase_done) && !(stop_e_0 && stop_o_0))
      correct0_34 <= 1'b0;
    else correct0_34 <= correct0_34;

    if (correct0_35 && (targetis_0  && p_trdy && !p_stop &&
!p_dphase_done) && !((!stop_e_0 || !stop_o_0 && stop_e_0)))
      correct0_35 <= 1'b0;
    else correct0_35 <= correct0_35;

    /* Once target has asserted stop, it cannot change devsel, trdy, or stop
 until the data phase compltes.*/

    if (correct0_36 && (targetis_0 && p_stop && !p_dphase_done) && !(stop_e_0 && stop_o_0))
      correct0_36 <= 1'b0;
    else correct0_36 <= correct0_36;

    if (correct0_37 && (targetis_0  && p_stop && p_devsel &&
!p_dphase_done) && !(devsel_e_0 && devsel_o_0))
      correct0_37 <= 1'b0;
    else correct0_37 <= correct0_37;

    if (correct0_38 && (targetis_0  && p_stop && p_trdy &&
!p_dphase_done) && !(trdy_e_0 && trdy_o_0))
      correct0_38 <= 1'b0;
    else correct0_38 <= correct0_38;

    if (correct0_39 && (targetis_0  && p_stop && !p_devsel &&
!p_dphase_done) && !((!devsel_e_0 || !devsel_o_0 && devsel_e_0)))
      correct0_39 <= 1'b0;
    else correct0_39 <= correct0_39;

    if (correct0_40 && (targetis_0  && p_stop && !p_trdy &&
!p_dphase_done) && !((!trdy_e_0 || !trdy_o_0 && trdy_e_0)))
      correct0_40 <= 1'b0;
    else correct0_40 <= correct0_40;

    /* trdy, stop and devsel must be deasserted the clock following the completion
 of the last data phase.*/

    if (correct0_41 && (targetis_0  && p_final_dphase_done) && !((!trdy_e_0 ||
!trdy_o_0 && trdy_e_0)))
      correct0_41 <= 1'b0;
    else correct0_41 <= correct0_41;

    if (correct0_42 && (targetis_0  && p_final_dphase_done) && !((!stop_e_0 ||
!stop_o_0 && stop_e_0)))
      correct0_42 <= 1'b0;
    else correct0_42 <= correct0_42;

    if (correct0_43 && (targetis_0  && p_final_dphase_done) && !((!devsel_e_0 ||
!devsel_o_0 && devsel_e_0)))
      correct0_43 <= 1'b0;
    else correct0_43 <= correct0_43;

    /* when both trdy and stop are asserted (together), trdy must be deasserted
 when the data phase completes.*/

    if (correct0_44 && (targetis_0  && p_stop && p_irdy &&
p_trdy) && !((!trdy_e_0 || !trdy_o_0 && trdy_e_0)))
      correct0_44 <= 1'b0;
    else correct0_44 <= correct0_44;

    /* before the target can signal target-abort, devsel must be asserted for one
 or more clocks.*/

    if (correct0_45 && (targetis_0  && !p_target_abort &&
!p_devsel) && !(!((!devsel_e_0 || !devsel_o_0 && devsel_e_0) && stop_e_0 &&
stop_o_0 && (!trdy_e_0 || !trdy_o_0 && trdy_e_0))))
      correct0_45 <= 1'b0;
    else correct0_45 <= correct0_45;

    /* target initial latency requirement.  target must respond within 16 clocks
 of frame being asserted.*/

    if (correct0_46 && (targetis_0  && p_t_initial == 15 && !p_stop &&
!p_trdy) && !((stop_e_0 && stop_o_0 || trdy_e_0 && trdy_o_0)))
      correct0_46 <= 1'b0;
    else correct0_46 <= correct0_46;

    /* target subsequent requirement.   target must respond within 8 clocks after
 the last data phase.*/

    if (correct0_47 && (targetis_0  && p_t_subseq == 7 && !p_stop &&
!p_trdy) && !((stop_e_0 && stop_o_0 || trdy_e_0 && trdy_o_0)))
      correct0_47 <= 1'b0;
    else correct0_47 <= correct0_47;

    /* Once devsel has been asserted, it cannot be deasserted until the last data
 phase has completed, except to signal target_abort.*/

    if (correct0_48 && (targetis_0  && p_devsel &&
!p_final_dphase_done) && !((devsel_e_0 && devsel_o_0 || stop_e_0 && stop_o_0
&& (!devsel_e_0 || !devsel_o_0 && devsel_e_0) && (!trdy_e_0 || !trdy_o_0 &&
trdy_e_0))))
      correct0_48 <= 1'b0;
    else correct0_48 <= correct0_48;

    /* devsel can only be asserted in the first four cycles since frame was
 asserted.   The statement is slightly stronger than what's in the spec.*/

    if (correct0_49 && (targetis_0  && !p_devsel && !((!(pp_frame) && p_frame ||
p_frame_7 > 0 && p_frame_7 < 4))) && !(!(devsel_e_0 && devsel_o_0)))
      correct0_49 <= 1'b0;
    else correct0_49 <= correct0_49;

    /* trdy, devsel and stop uses the address phase as a turnaround cycle when
   this is not a b2b transaction.  (3.6.1 p89 2.2)*/

    if (correct0_50 && (p_idle) && !(!devsel_e_0 && !stop_e_0 && !trdy_e_0)) correct0_50 <= 1'b0;
    else correct0_50 <= correct0_50;

    /* For during the transaction except the first two phases.  Also includes
   the first phase of idle.  This subsumes the mutual exclusion property of
   the bus.  The second rule works for b2bs since the master needs to be
   the same for the second transaction.  The third rule is needed to cover
   the missing case of the address phase for a b2b immediately after a read
   transaction.*/

    if (correct0_51 && (!(!(pp_frame) && p_frame) && !p_idle && !masteris_0
) && !(!frame_e_0 && !irdy_e_0 && !cbe_e_0))
      correct0_51 <= 1'b0;
    else correct0_51 <= correct0_51;

    if (correct0_52 && (!(!(pp_frame) && p_frame) && !p_idle && !masteris_0  &&
p_in_write_tran) && !(!ad_e_0))
      correct0_52 <= 1'b0;
    else correct0_52 <= correct0_52;

    if (correct0_53 && (p_final_dphase_done && !masteris_0 && p_in_read_tran) && !(!ad_e_0))
      correct0_53 <= 1'b0;
    else correct0_53 <= correct0_53;

    /* For during the address phase for a non-b2b.  irdy is not to be driven
   immediately following an idle.*/

    if (correct0_54 && (p_idle && !p_gnt_0) && !(!ad_e_0 && !cbe_e_0 && !frame_e_0))
      correct0_54 <= 1'b0;
    else correct0_54 <= correct0_54;

    /* For the phase right after the address phase.  */

    if (correct0_55 && (!(pp_frame) && p_frame && !(pp_gnt_0 )) && !(!frame_e_0
&& !irdy_e_0 && !cbe_e_0 && !ad_e_0))
      correct0_55 <= 1'b0;
    else correct0_55 <= correct0_55;

    /* Before an agent can stop driving a line, it must deassert it (pull it
   up).*/

    if (correct0_56 && (p_frame_e_0 && p_frame_o_0) && !(frame_e_0)) correct0_56 <= 1'b0;
    else correct0_56 <= correct0_56;

    if (correct0_57 && (p_irdy_e_0 && p_irdy_o_0) && !(irdy_e_0)) correct0_57 <= 1'b0;
    else correct0_57 <= correct0_57;

    /* Before an agent can start driving a line, it must have been tristated
   (not driven) for at least one clock.*/

    if (correct0_58 && (!p_frame_e_0 && (p_frame_e_1 || p_frame_e_0)) && !(!frame_e_0))
      correct0_58 <= 1'b0;
    else correct0_58 <= correct0_58;

    if (correct0_59 && (!p_irdy_e_0 && (p_irdy_e_1 || p_irdy_e_0)) && !(!irdy_e_0))
      correct0_59 <= 1'b0;
    else correct0_59 <= correct0_59;

    /* For during the transaction except the first two phases.  Also includes
   the first phase of idle.   For the second statement, it does not apply
   for the first phase of idle because a b2b might come after.*/

    if (correct0_60 && (!(!(pp_frame) && p_frame) && !p_idle && !targetis_0
) && !(!trdy_e_0 && !stop_e_0 && !devsel_e_0))
      correct0_60 <= 1'b0;
    else correct0_60 <= correct0_60;

    if (correct0_61 && (!(!(pp_frame) && p_frame) && !p_idle &&
!p_final_dphase_done && !targetis_0  && p_in_read_tran) && !(!ad_e_0))
      correct0_61 <= 1'b0;
    else correct0_61 <= correct0_61;

    /* For the phase right after the address phase.  */

    if (correct0_62 && (!(pp_frame) && p_frame && !p_t_sel_0 &&
!p_idsel_0) && !(!devsel_e_0 && !stop_e_0 && !trdy_e_0))
      correct0_62 <= 1'b0;
    else correct0_62 <= correct0_62;

    /* Before an agent can stop driving a line, it must deassert it (pull it
   up). */

    if (correct0_63 && (p_devsel_e_0 && p_devsel_o_0) && !(devsel_e_0)) correct0_63 <= 1'b0;
    else correct0_63 <= correct0_63;

    if (correct0_64 && (p_trdy_e_0 && p_trdy_o_0) && !(trdy_e_0)) correct0_64 <= 1'b0;
    else correct0_64 <= correct0_64;

    if (correct0_65 && (p_stop_e_0 && p_stop_o_0) && !(stop_e_0)) correct0_65 <= 1'b0;
    else correct0_65 <= correct0_65;

    /* Before an agent can start driving a line, it must have been tristated
   (not driven) for at least one clock. */

    if (correct0_66 && (!p_devsel_e_0 && (p_devsel_e_1 || p_devsel_e_0)) && !(!devsel_e_0))
      correct0_66 <= 1'b0;
    else correct0_66 <= correct0_66;

    if (correct0_67 && (!p_trdy_e_0 && (p_trdy_e_1 || p_trdy_e_0)) && !(!trdy_e_0))
      correct0_67 <= 1'b0;
    else correct0_67 <= correct0_67;

    if (correct0_68 && (!p_stop_e_0 && (p_stop_e_1 || p_stop_e_0)) && !(!stop_e_0))
      correct0_68 <= 1'b0;
    else correct0_68 <= correct0_68;

    // For agent 1

    if (correct1_0 && (gnt_1) && !(!gnt_0)) correct1_0 <= 1'b0;
    else correct1_0 <= correct1_0;

    /* if in idle, there must be a one clock delay between deasserting one gnt
  and asserting another gnt.  This is because of address stepping. */

    if (correct1_1 && (p_idle && p_gnt_1) && !((gnt_1 || !gnt_1 && !gnt_0))) correct1_1 <= 1'b0;
    else correct1_1 <= correct1_1;

    /* if gnt is given to something that didn't request it, it must be because
     of arbitration parking where no agents are requesting the bus.*/

    if (correct1_2 && (!p_gnt_1 && !p_req_1 && (p_req_1 || p_req_0)) && !(!gnt_1))
      correct1_2 <= 1'b0;
    else correct1_2 <= correct1_2;

    /* the cbe buffers must remain enabled from the first clock of the data
 phase through the end of the transaction.  */

    if (correct1_3 && (masteris_1 && !p_final_dphase_done && !p_idle) && !(cbe_e_1))
      correct1_3 <= 1'b0;
    else correct1_3 <= correct1_3;

    /* during a write cycle, whenever irdy is asserted, then the bus is driven by
 master.  The "!in_addr_phase" is needed because the master_is value and
 in_write_tran value are not valid during the address phase.*/

    if (correct1_4 && (masteris_1  && irdy_e_1 && irdy_o_1 && in_write_tran &&
!in_addr_phase) && !(ad_e_1))
      correct1_4 <= 1'b0;
    else correct1_4 <= correct1_4;

    /* only when IRDY is asserted can FRAME be deasserted.*/

    if (correct1_5 && (masteris_1  && p_frame) && !((frame_e_1 && frame_o_1 ||
irdy_e_1 && irdy_o_1)))
      correct1_5 <= 1'b0;
    else correct1_5 <= correct1_5;

    /* if frame does deassert and irdy wasn't asserted on the same clock *and* a
 data phase hasn't just completed, the following master abort conditions
 must hold.  (frame changing by deasserting)*/

    if (correct1_6 && (masteris_1  && !((p_stop || p_trdy)) && p_frame && p_irdy
&& (((p_devsel || p_devsel_history) || !p_initial_data_phase) ||
!(p_frame_7 >= 4))) && !(frame_e_1 && frame_o_1))
      correct1_6 <= 1'b0;
    else correct1_6 <= correct1_6;

    /* once irdy is asserted, it can only deassert without a dphase done, if a
 master abort has happened.  We must consider the case where the
 transaction attempted was a one data phase one.*/

    if (correct1_7 && (masteris_1  && p_irdy && !((p_stop || p_trdy)) &&
(((p_devsel || p_devsel_history) || !p_initial_data_phase) ||
!(p_frame_7 >= 4))) && !((irdy_e_1 && irdy_o_1 || m_abort)))
      correct1_7 <= 1'b0;
    else correct1_7 <= correct1_7;

    /* master must raise irdy within 8 cycles of the assertion of frame.*/

    if (correct1_8 && (masteris_1 && p_m_initial == 7 && !p_irdy) && !(irdy_e_1 && irdy_o_1))
      correct1_8 <= 1'b0;
    else correct1_8 <= correct1_8;

    /* master must raise irdy within 8 cycles of the last data completion.*/

    if (correct1_9 && (masteris_1 && p_m_subseq == 7 && !p_irdy) && !(irdy_e_1 && irdy_o_1))
      correct1_9 <= 1'b0;
    else correct1_9 <= correct1_9;

    /* For a timeout situation, the master must not delay the assertion of irdy.
 termination can be delayed if IRDY# is deasserted because FRAME# cannot be
 deasserted until IRDY# is asserted.  "This delay in termination should not
 be extended more than two or three clocks." after GNT# has been
 deasserted.  (3.3.3.1 p39) (internal counter)*/

    if (correct1_10 && (masteris_1 && p_m_irdy_timeout == 3 && !p_irdy) && !(irdy_e_1 && irdy_o_1))
      correct1_10 <= 1'b0;
    else correct1_10 <= correct1_10;

    /* once irdy is asserted, frame can never change from deasserted to asserted
 until the data phase completes.*/

    if (correct1_11 && (masteris_1  && p_irdy && !p_frame &&
!p_dphase_done) && !((!frame_e_1 || !frame_o_1 && frame_e_1)))
      correct1_11 <= 1'b0;
    else correct1_11 <= correct1_11;

    /* if gnt is deasserted before the natural completion of the transaction and
 there is a timeout, continued use of the bus is not allowed.
 1. If a data phase has just completed, the next data phase cannot be a non
 m_term one.
 2. If irdy is deasserted, the next data phase cannot be a non m_term one.
 3. If frame and irdy are both asserted and a master abort is allowed to
 happen, the master must master abort.*/

    if (correct1_12 && (masteris_1  && p_timeout && !p_gnt_1 && p_dphase_done &&
p_frame && p_irdy) && !(!(frame_e_1 && frame_o_1 && irdy_e_1 && irdy_o_1)))
      correct1_12 <= 1'b0;
    else correct1_12 <= correct1_12;

    if (correct1_13 && (masteris_1  && p_timeout && !p_gnt_1 && p_frame &&
!p_irdy) && !(!(frame_e_1 && frame_o_1 && irdy_e_1 && irdy_o_1)))
      correct1_13 <= 1'b0;
    else correct1_13 <= correct1_13;

    if (correct1_14 && (masteris_1  && p_timeout && !p_gnt_1 && p_frame && p_irdy
&& !p_devsel && !p_devsel_history) && !((!frame_e_1 || !frame_o_1 &&
frame_e_1)))
      correct1_14 <= 1'b0;
    else correct1_14 <= correct1_14;

    /* Whenever stop is asserted, the master must deassert frame as soon as irdy
 is asserted.*/

    if (correct1_15 && (masteris_1  && p_stop && !p_irdy) && !(!(frame_e_1 &&
frame_o_1 && irdy_e_1 && irdy_o_1)))
      correct1_15 <= 1'b0;
    else correct1_15 <= correct1_15;

    if (correct1_16 && (masteris_1  && p_stop && p_irdy &&
p_dphase_done) && !(!(frame_e_1 && frame_o_1 && irdy_e_1 && irdy_o_1)))
      correct1_16 <= 1'b0;
    else correct1_16 <= correct1_16;

    /* irdy must be deasserted the clock following the completion of the last data
 phase.*/

    if (correct1_17 && (masteris_1  && p_final_dphase_done) && !((!irdy_e_1 ||
!irdy_o_1 && irdy_e_1)))
      correct1_17 <= 1'b0;
    else correct1_17 <= correct1_17;

    /* if a stop had happened, req must be deasserted on the clock the bus
 becomes idle and also either the clock before or clocks after.  */

    if (correct1_18 && (masteris_1  && p_devsel && pp_stop && p_stop &&
p_final_dphase_done) && !(!req_1))
      correct1_18 <= 1'b0;
    else correct1_18 <= correct1_18;

    /* scenario a : there must be an idle after a transaction terminated by a
 retry or disconnect.  This is hard to assign blame so break it up.*/

    if (correct1_19 && (masteris_1  && p_devsel && pp_stop && p_stop &&
p_final_dphase_done) && !((!frame_e_1 || !frame_o_1 && frame_e_1) &&
(!irdy_e_1 || !irdy_o_1 && irdy_e_1)))
      correct1_19 <= 1'b0;
    else correct1_19 <= correct1_19;

    /* cbes must be enabled during the address phase to issue the trans
   command.*/

    if (correct1_20 && (!p_frame) && !((!(frame_e_1 && frame_o_1) || cbe_e_1))) correct1_20 <= 1'b0;
    else correct1_20 <= correct1_20;

    /* during the address phase, AD is driven by the master.*/

    if (correct1_21 && (!p_frame) && !((!(frame_e_1 && frame_o_1) || ad_e_1))) correct1_21 <= 1'b0;
    else correct1_21 <= correct1_21;

    /* a turnaround cycle is required for a read.  (Required for both the
   target and the master.)*/

    if (correct1_22 && (p_in_addr_phase && p_read_command) && !(!ad_e_1)) correct1_22 <= 1'b0;
    else correct1_22 <= correct1_22;

    /* ad and cbe use the idle state as their turnaround cycle.*/

    if (correct1_23 && (!in_read_tran && !irdy_e_1 && !frame_e_1) && !(!cbe_e_1 && !ad_e_1))
      correct1_23 <= 1'b0;
    else correct1_23 <= correct1_23;

    /* the addr phase is a turnaround cycle for irdy when the transaction is not
   a b2b.*/

    if (correct1_24 && (p_idle) && !(!irdy_e_1)) correct1_24 <= 1'b0;
    else correct1_24 <= correct1_24;

    /* cannot be both a read command and a write command.  This is not really a
   PCI spec but is a fact and is needed for verifying this spec.*/

    if (correct1_25 && (!p_frame) && !((!(frame_e_1 && frame_o_1) ||
!(read_command && write_command))))
      correct1_25 <= 1'b0;
    else correct1_25 <= correct1_25;

    /* it is either a write command or a read command.
   This is not really a PCI spec but is a fact and is needed for verifying
   this spec.*/

    if (correct1_26 && (!p_frame) && !((!(frame_e_1 && frame_o_1) ||
(read_command || write_command))))
      correct1_26 <= 1'b0;
    else correct1_26 <= correct1_26;

    /* can only start a transaction if gnt is high.  Cover b2b case.*/

    if (correct1_27 && (!p_frame && !p_gnt_1) && !(!(frame_e_1 && frame_o_1))) correct1_27 <= 1'b0;
    else correct1_27 <= correct1_27;

    /*frame & !idle & !final_dphase_done -> next(!assert(i, frame));*/

    if (correct1_28 && (!p_frame && p_irdy && !((p_trdy ||
p_stop))) && !(!(frame_e_1 && frame_o_1)))
      correct1_28 <= 1'b0;
    else correct1_28 <= correct1_28;

    /* turnaround cycle enforced by a deasserted trdy.  In this phase, it can be
 driven deasserted, or floated deasserted.*/

    if (correct1_29 && (targetis_1  && p_read_command &&
p_in_addr_phase) && !((!trdy_e_1 || !trdy_o_1 && trdy_e_1)))
      correct1_29 <= 1'b0;
    else correct1_29 <= correct1_29;

    /* target can only assert trdy if devsel is asserted.  This also stipulates
 that an agent can only assert trdy if it had claimed the transaction by
 asserting devsel.  */

    if (correct1_30 && (targetis_1 && trdy_e_1 && trdy_o_1) && !(devsel_e_1 && devsel_o_1))
      correct1_30 <= 1'b0;
    else correct1_30 <= correct1_30;

    /* Once stop is asserted, it must remain asserted until frame is
 deasserted.  */

    if (correct1_31 && (targetis_1 && p_stop && p_frame) && !(stop_e_1 && stop_o_1))
      correct1_31 <= 1'b0;
    else correct1_31 <= correct1_31;

    /* Once frame is deasserted, stop must be deasserted.  */

    if (correct1_32 && (targetis_1  && pp_frame && !p_frame) && !((!stop_e_1 ||
!stop_o_1 && stop_e_1)))
      correct1_32 <= 1'b0;
    else correct1_32 <= correct1_32;

    /* Once target has asserted trdy, it cannot change devsel, trdy, or stop
 until the data phase compeltes.  (devsel rule already implied by rest.)*/

    if (correct1_33 && (targetis_1 && p_trdy && !p_dphase_done) && !(trdy_e_1 && trdy_o_1))
      correct1_33 <= 1'b0;
    else correct1_33 <= correct1_33;

    if (correct1_34 && (targetis_1  && p_trdy && p_stop &&
!p_dphase_done) && !(stop_e_1 && stop_o_1))
      correct1_34 <= 1'b0;
    else correct1_34 <= correct1_34;

    if (correct1_35 && (targetis_1  && p_trdy && !p_stop &&
!p_dphase_done) && !((!stop_e_1 || !stop_o_1 && stop_e_1)))
      correct1_35 <= 1'b0;
    else correct1_35 <= correct1_35;

    /* Once target has asserted stop, it cannot change devsel, trdy, or stop
 until the data phase compltes.*/

    if (correct1_36 && (targetis_1 && p_stop && !p_dphase_done) && !(stop_e_1 && stop_o_1))
      correct1_36 <= 1'b0;
    else correct1_36 <= correct1_36;

    if (correct1_37 && (targetis_1  && p_stop && p_devsel &&
!p_dphase_done) && !(devsel_e_1 && devsel_o_1))
      correct1_37 <= 1'b0;
    else correct1_37 <= correct1_37;

    if (correct1_38 && (targetis_1  && p_stop && p_trdy &&
!p_dphase_done) && !(trdy_e_1 && trdy_o_1))
      correct1_38 <= 1'b0;
    else correct1_38 <= correct1_38;

    if (correct1_39 && (targetis_1  && p_stop && !p_devsel &&
!p_dphase_done) && !((!devsel_e_1 || !devsel_o_1 && devsel_e_1)))
      correct1_39 <= 1'b0;
    else correct1_39 <= correct1_39;

    if (correct1_40 && (targetis_1  && p_stop && !p_trdy &&
!p_dphase_done) && !((!trdy_e_1 || !trdy_o_1 && trdy_e_1)))
      correct1_40 <= 1'b0;
    else correct1_40 <= correct1_40;

    /* trdy, stop and devsel must be deasserted the clock following the completion
 of the last data phase.*/

    if (correct1_41 && (targetis_1  && p_final_dphase_done) && !((!trdy_e_1 ||
!trdy_o_1 && trdy_e_1)))
      correct1_41 <= 1'b0;
    else correct1_41 <= correct1_41;

    if (correct1_42 && (targetis_1  && p_final_dphase_done) && !((!stop_e_1 ||
!stop_o_1 && stop_e_1)))
      correct1_42 <= 1'b0;
    else correct1_42 <= correct1_42;

    if (correct1_43 && (targetis_1  && p_final_dphase_done) && !((!devsel_e_1 ||
!devsel_o_1 && devsel_e_1)))
      correct1_43 <= 1'b0;
    else correct1_43 <= correct1_43;

    /* when both trdy and stop are asserted (together), trdy must be deasserted
 when the data phase completes.*/

    if (correct1_44 && (targetis_1  && p_stop && p_irdy &&
p_trdy) && !((!trdy_e_1 || !trdy_o_1 && trdy_e_1)))
      correct1_44 <= 1'b0;
    else correct1_44 <= correct1_44;

    /* before the target can signal target-abort, devsel must be asserted for one
 or more clocks.*/

    if (correct1_45 && (targetis_1  && !p_target_abort &&
!p_devsel) && !(!((!devsel_e_1 || !devsel_o_1 && devsel_e_1) && stop_e_1 &&
stop_o_1 && (!trdy_e_1 || !trdy_o_1 && trdy_e_1))))
      correct1_45 <= 1'b0;
    else correct1_45 <= correct1_45;

    /* target initial latency requirement.  target must respond within 16 clocks
 of frame being asserted.*/

    if (correct1_46 && (targetis_1  && p_t_initial == 15 && !p_stop &&
!p_trdy) && !((stop_e_1 && stop_o_1 || trdy_e_1 && trdy_o_1)))
      correct1_46 <= 1'b0;
    else correct1_46 <= correct1_46;

    /* target subsequent requirement.   target must respond within 8 clocks after
 the last data phase.*/

    if (correct1_47 && (targetis_1  && p_t_subseq == 7 && !p_stop &&
!p_trdy) && !((stop_e_1 && stop_o_1 || trdy_e_1 && trdy_o_1)))
      correct1_47 <= 1'b0;
    else correct1_47 <= correct1_47;

    /* Once devsel has been asserted, it cannot be deasserted until the last data
 phase has completed, except to signal target_abort.*/

    if (correct1_48 && (targetis_1  && p_devsel &&
!p_final_dphase_done) && !((devsel_e_1 && devsel_o_1 || stop_e_1 && stop_o_1
&& (!devsel_e_1 || !devsel_o_1 && devsel_e_1) && (!trdy_e_1 || !trdy_o_1 &&
trdy_e_1))))
      correct1_48 <= 1'b0;
    else correct1_48 <= correct1_48;

    /* devsel can only be asserted in the first four cycles since frame was
 asserted.   The statement is slightly stronger than what's in the spec.*/

    if (correct1_49 && (targetis_1  && !p_devsel && !((!(pp_frame) && p_frame ||
p_frame_7 > 0 && p_frame_7 < 4))) && !(!(devsel_e_1 && devsel_o_1)))
      correct1_49 <= 1'b0;
    else correct1_49 <= correct1_49;

    /* trdy, devsel and stop uses the address phase as a turnaround cycle when
   this is not a b2b transaction.  (3.6.1 p89 2.2)*/

    if (correct1_50 && (p_idle) && !(!devsel_e_1 && !stop_e_1 && !trdy_e_1)) correct1_50 <= 1'b0;
    else correct1_50 <= correct1_50;

    /* For during the transaction except the first two phases.  Also includes
   the first phase of idle.  This subsumes the mutual exclusion property of
   the bus.  The second rule works for b2bs since the master needs to be
   the same for the second transaction.  The third rule is needed to cover
   the missing case of the address phase for a b2b immediately after a read
   transaction.*/

    if (correct1_51 && (!(!(pp_frame) && p_frame) && !p_idle && !masteris_1
) && !(!frame_e_1 && !irdy_e_1 && !cbe_e_1))
      correct1_51 <= 1'b0;
    else correct1_51 <= correct1_51;

    if (correct1_52 && (!(!(pp_frame) && p_frame) && !p_idle && !masteris_1  &&
p_in_write_tran) && !(!ad_e_1))
      correct1_52 <= 1'b0;
    else correct1_52 <= correct1_52;

    if (correct1_53 && (p_final_dphase_done && !masteris_1 && p_in_read_tran) && !(!ad_e_1))
      correct1_53 <= 1'b0;
    else correct1_53 <= correct1_53;

    /* For during the address phase for a non-b2b.  irdy is not to be driven
   immediately following an idle.*/

    if (correct1_54 && (p_idle && !p_gnt_1) && !(!ad_e_1 && !cbe_e_1 && !frame_e_1))
      correct1_54 <= 1'b0;
    else correct1_54 <= correct1_54;

    /* For the phase right after the address phase.  */

    if (correct1_55 && (!(pp_frame) && p_frame && !(pp_gnt_1 )) && !(!frame_e_1
&& !irdy_e_1 && !cbe_e_1 && !ad_e_1))
      correct1_55 <= 1'b0;
    else correct1_55 <= correct1_55;

    /* Before an agent can stop driving a line, it must deassert it (pull it
   up).*/

    if (correct1_56 && (p_frame_e_1 && p_frame_o_1) && !(frame_e_1)) correct1_56 <= 1'b0;
    else correct1_56 <= correct1_56;

    if (correct1_57 && (p_irdy_e_1 && p_irdy_o_1) && !(irdy_e_1)) correct1_57 <= 1'b0;
    else correct1_57 <= correct1_57;

    /* Before an agent can start driving a line, it must have been tristated
   (not driven) for at least one clock.*/

    if (correct1_58 && (!p_frame_e_1 && (p_frame_e_1 || p_frame_e_0)) && !(!frame_e_1))
      correct1_58 <= 1'b0;
    else correct1_58 <= correct1_58;

    if (correct1_59 && (!p_irdy_e_1 && (p_irdy_e_1 || p_irdy_e_0)) && !(!irdy_e_1))
      correct1_59 <= 1'b0;
    else correct1_59 <= correct1_59;

    /* For during the transaction except the first two phases.  Also includes
   the first phase of idle.   For the second statement, it does not apply
   for the first phase of idle because a b2b might come after.*/

    if (correct1_60 && (!(!(pp_frame) && p_frame) && !p_idle && !targetis_1
) && !(!trdy_e_1 && !stop_e_1 && !devsel_e_1))
      correct1_60 <= 1'b0;
    else correct1_60 <= correct1_60;

    if (correct1_61 && (!(!(pp_frame) && p_frame) && !p_idle &&
!p_final_dphase_done && !targetis_1  && p_in_read_tran) && !(!ad_e_1))
      correct1_61 <= 1'b0;
    else correct1_61 <= correct1_61;

    /* For the phase right after the address phase.  */

    if (correct1_62 && (!(pp_frame) && p_frame && !p_t_sel_1 &&
!p_idsel_1) && !(!devsel_e_1 && !stop_e_1 && !trdy_e_1))
      correct1_62 <= 1'b0;
    else correct1_62 <= correct1_62;

    /* Before an agent can stop driving a line, it must deassert it (pull it
   up). */

    if (correct1_63 && (p_devsel_e_1 && p_devsel_o_1) && !(devsel_e_1)) correct1_63 <= 1'b0;
    else correct1_63 <= correct1_63;

    if (correct1_64 && (p_trdy_e_1 && p_trdy_o_1) && !(trdy_e_1)) correct1_64 <= 1'b0;
    else correct1_64 <= correct1_64;

    if (correct1_65 && (p_stop_e_1 && p_stop_o_1) && !(stop_e_1)) correct1_65 <= 1'b0;
    else correct1_65 <= correct1_65;

    /* Before an agent can start driving a line, it must have been tristated
   (not driven) for at least one clock. */

    if (correct1_66 && (!p_devsel_e_1 && (p_devsel_e_1 || p_devsel_e_0)) && !(!devsel_e_1))
      correct1_66 <= 1'b0;
    else correct1_66 <= correct1_66;

    if (correct1_67 && (!p_trdy_e_1 && (p_trdy_e_1 || p_trdy_e_0)) && !(!trdy_e_1))
      correct1_67 <= 1'b0;
    else correct1_67 <= correct1_67;

    if (correct1_68 && (!p_stop_e_1 && (p_stop_e_1 || p_stop_e_0)) && !(!stop_e_1))
      correct1_68 <= 1'b0;
    else correct1_68 <= correct1_68;


    // The statements which update the p_ and pp_ variables

    p_gnt_1 <= gnt_1;
    p_frame_o_1 <= frame_o_1;
    p_irdy_o_1 <= irdy_o_1;
    p_t_sel_1 <= t_sel_1;
    p_idsel_1 <= idsel_1;
    p_devsel_o_1 <= devsel_o_1;
    p_trdy_o_1 <= trdy_o_1;
    p_stop_o_1 <= stop_o_1;
    p_req_1 <= req_1;
    p_req_0 <= req_0;
    p_initial_data_phase <= initial_data_phase;
    p_m_initial <= m_initial;
    p_m_subseq <= m_subseq;
    p_m_irdy_timeout <= m_irdy_timeout;
    p_timeout <= timeout;
    p_devsel_history <= devsel_history;
    p_read_command <= read_command;
    p_in_addr_phase <= in_addr_phase;
    p_dphase_done <= dphase_done;
    p_irdy <= irdy;
    p_target_abort <= target_abort;
    p_t_initial <= t_initial;
    p_t_subseq <= t_subseq;
    p_stop <= stop;
    p_trdy <= trdy;
    p_devsel <= devsel;
    p_frame_7 <= frame_7;
    p_in_write_tran <= in_write_tran;
    p_gnt_0 <= gnt_0;
    p_frame_o_0 <= frame_o_0;
    p_irdy_o_0 <= irdy_o_0;
    p_frame_e_1 <= frame_e_1;
    p_frame_e_0 <= frame_e_0;
    p_irdy_e_1 <= irdy_e_1;
    p_irdy_e_0 <= irdy_e_0;
    p_idle <= idle;
    p_final_dphase_done <= final_dphase_done;
    p_in_read_tran <= in_read_tran;
    p_frame <= frame;
    p_t_sel_0 <= t_sel_0;
    p_idsel_0 <= idsel_0;
    p_devsel_o_0 <= devsel_o_0;
    p_trdy_o_0 <= trdy_o_0;
    p_stop_o_0 <= stop_o_0;
    p_devsel_e_1 <= devsel_e_1;
    p_devsel_e_0 <= devsel_e_0;
    p_trdy_e_1 <= trdy_e_1;
    p_trdy_e_0 <= trdy_e_0;
    p_stop_e_1 <= stop_e_1;
    p_stop_e_0 <= stop_e_0;
    pp_gnt_1 <= p_gnt_1;
    pp_stop <= p_stop;
    pp_gnt_0 <= p_gnt_0;
    pp_frame <= p_frame;

    // Statements for updating the masteris variables

    if (!p_frame && frame && frame_e_0 && frame_o_0) masteris_0 <= 1'b1;
    else if (masteris_0 && (idle || final_dphase_done)) masteris_0 <= 1'b0;
    else masteris_0 <= masteris_0;

    if (!p_frame && frame && frame_e_1 && frame_o_1) masteris_1 <= 1'b1;
    else if (masteris_1 && (idle || final_dphase_done)) masteris_1 <= 1'b0;
    else masteris_1 <= masteris_1;


    // Statements for updating the targetis variables

    if (in_addr_phase && is_cbe_com && idsel_0 || in_addr_phase && !is_cbe_com && t_sel_0)
      targetis_0 <= 1'b1;
    else if (targetis_0 && (idle || final_dphase_done)) targetis_0 <= 1'b0;
    else targetis_0 <= targetis_0;

    if (in_addr_phase && is_cbe_com && idsel_1 || in_addr_phase && !is_cbe_com && t_sel_1)
      targetis_1 <= 1'b1;
    else if (targetis_1 && (idle || final_dphase_done)) targetis_1 <= 1'b0;
    else targetis_1 <= targetis_1;



  end
  // END MAIN BLOCK

endmodule
