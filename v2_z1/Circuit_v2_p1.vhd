library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity Circuit_v2_p1 is
port(
     rst : in std_logic;
     clk : in std_logic;
     a : in std_logic;
     b : in std_logic;
     c : in std_logic;
     d : in std_logic;
     e : in std_logic;
     f : in std_logic;
     g : in std_logic;
     h : in std_logic;
     out1 : out std_logic;
     out2 : out std_logic
 );
end Circuit_v2_p1;

architecture Behavioral of Circuit_v2_p1 is

component lut3 is
 generic(INIT : std_logic_vector(7 downto 0));
 port(
     I2 : in std_logic;
     I1 : in std_logic;
     I0 : in std_logic;
     O : out std_logic
 );

end component;

signal lut1_6, lut2_6, lut3_5, lut4_5, lut5_6 : std_logic;
signal out1_reg, out1_next : std_logic;
signal out2_reg, out2_next : std_logic;

begin

reg_proc : process(clk, rst)
 begin
     if (rst = '1') then
         out1_reg <= '0';
         out2_reg <= '0';
     elsif rising_edge(clk) then
         out1_reg <= out1_next;
         out2_reg <= out2_next;
     end if;
 end process reg_proc;
 
 out1 <= out1_reg;

 out2 <= out2_reg;
 out1_next <= not (not (not (not (b) and not (c) and not (g and b) and (not (g and h))) and a) and not (d and e and f));
 
 look_up_table_1 : lut3
 generic map(INIT => "11100000")
 port map(
         I0 => c,
         I1 => b,
         I2 => a,
         O => lut1_6);
         
 look_up_table_2 : lut3
 generic map(INIT => "10000000")
 port map(
         I0 => f,
         I1 => e,
         I2 => d,
         O => lut2_6);
         
 look_up_table_3 : lut3
 generic map(INIT => "10000000")
 port map(
         I0 => b,
         I1 => g,
         I2 => a,
         O => lut3_5);
 
 look_up_table_4 : lut3
 generic map(INIT => "10000000")
 port map(
         I0 => h,
         I1 => g,
         I2 => a,
         O => lut4_5);
         
 look_up_table_5 : lut3
 generic map(INIT => "11111110")
 port map(
         I0 => lut4_5,
         I1 => lut3_5,
         I2 => '0',
         O => lut5_6);
         
 look_up_table_6 : lut3
 generic map(INIT => "11111110")
 port map(
         I0 => lut5_6,
         I1 => lut2_6,
         I2 => lut1_6,
         O => out2_next);
        
end Behavioral;
