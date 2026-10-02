module Bus (
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
    cbe_o_0,
    ad_o_0,

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
    cbe_o_1,
    ad_o_1
);


  output frame;
  output irdy;
  output trdy;
  output stop;
  output devsel;
  output [3:0] cbe;
  output [31:0] ad;

  wire frame;
  wire irdy;
  wire trdy;
  wire stop;
  wire devsel;
  wire [3:0] cbe;
  wire [31:0] ad;

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
  input [3:0] cbe_o_0;
  input [31:0] ad_o_0;

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
  input [3:0] cbe_o_1;
  input [31:0] ad_o_1;

  buswire frame_wired (
      frame_e_0,
      frame_e_1,
      frame_o_0,
      frame_o_1,
      frame
  );
  buswire irdy_wired (
      irdy_e_0,
      irdy_e_1,
      irdy_o_0,
      irdy_o_1,
      irdy
  );
  buswire trdy_wired (
      trdy_e_0,
      trdy_e_1,
      trdy_o_0,
      trdy_o_1,
      trdy
  );
  buswire devsel_wired (
      devsel_e_0,
      devsel_e_1,
      devsel_o_0,
      devsel_o_1,
      devsel
  );
  buswire stop_wired (
      stop_e_0,
      stop_e_1,
      stop_o_0,
      stop_o_1,
      stop
  );

  buswire cbe_wired0 (
      cbe_e_0,
      cbe_e_1,
      cbe_o_0[0],
      cbe_o_1[0],
      cbe[0]
  );
  buswire cbe_wired1 (
      cbe_e_0,
      cbe_e_1,
      cbe_o_0[1],
      cbe_o_1[1],
      cbe[1]
  );
  buswire cbe_wired2 (
      cbe_e_0,
      cbe_e_1,
      cbe_o_0[2],
      cbe_o_1[2],
      cbe[2]
  );
  buswire cbe_wired3 (
      cbe_e_0,
      cbe_e_1,
      cbe_o_0[3],
      cbe_o_1[3],
      cbe[3]
  );

  buswire ad_wired0 (
      ad_e_0,
      ad_e_1,
      ad_o_0[0],
      ad_o_1[0],
      ad[0]
  );
  buswire ad_wired1 (
      ad_e_0,
      ad_e_1,
      ad_o_0[1],
      ad_o_1[1],
      ad[1]
  );
  buswire ad_wired2 (
      ad_e_0,
      ad_e_1,
      ad_o_0[2],
      ad_o_1[2],
      ad[2]
  );
  buswire ad_wired3 (
      ad_e_0,
      ad_e_1,
      ad_o_0[3],
      ad_o_1[3],
      ad[3]
  );

  assign ad[31:4] = 0;

endmodule
