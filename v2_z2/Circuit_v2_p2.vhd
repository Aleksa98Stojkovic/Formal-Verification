library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;


entity Circuit_v2_p2 is
    Port(a, b, c, d, e, f : in std_logic;
         clk_i, rst_i : in std_logic;
         o1, o2 : out std_logic);
end Circuit_v2_p2;

architecture Behavioral of Circuit_v2_p2 is

-- MUX --
signal mux_i : std_logic_vector(7 downto 0);
signal sel_i : std_logic_vector(2 downto 0);
signal mux_o : std_logic;

-- D FF --
signal d_1, d_2, q_1, q_2 : std_logic;

-- LUTs --
signal lut1, lut2, lut3, lut4 : std_logic_vector(3 downto 0);
signal lut_o_1, lut_o_2, lut_o_3, lut_o_4 : std_logic;

begin

-- D FF --
D_FF: process(clk_i)
begin
    if(rising_edge(clk_i)) then
        if(rst_i = '1') then
            q_1 <= '0';
            q_2 <= '0';
        else
            q_1 <= d_1;
            q_2 <= d_2;
        end if;
    end if;
end process;

-- First Circuit --
mux_i(7 downto 4) <= "0101";
mux_i(3 downto 0) <= a & c & b & b;
sel_i <= d & e & f;
o1 <= q_1;
d_1 <= mux_o;

-- MUX --
mux_o <= mux_i(to_integer(unsigned(sel_i)));

-------------------

-- Second Circuit --
lut1 <= b & d & e & f;
lut2 <= a & d & e & f;
lut3 <= c & d & e & f;
lut4 <= '0' & lut_o_2 & lut_o_1 & lut_o_3;
d_2 <= lut_o_4;
o2 <= q_2;

LUT_1: entity work.Generic_LUT(Behavioral)
generic map(init => "0101001101010000")
port map(a_i => lut1, b_o =>lut_o_1);

LUT_2: entity work.Generic_LUT(Behavioral)
generic map(init => "0000100000000000")
port map(a_i => lut2, b_o =>lut_o_2);

LUT_3: entity work.Generic_LUT(Behavioral)
generic map(init => "0000010000000000")
port map(a_i => lut3, b_o =>lut_o_3);

LUT_4: entity work.Generic_LUT(Behavioral)
generic map(init => "1111111111111110")
port map(a_i => lut4, b_o =>lut_o_4);

-------------------

end Behavioral;
