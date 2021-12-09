library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity Circuit_v1_p2 is
    Port(a, b, c, d, e, f, g, h : in std_logic;
         clk_i, rst_i : in std_logic;
         o1, o2 : out std_logic);
end Circuit_v1_p2;

architecture Behavioral of Circuit_v1_p2 is

component generic_dec is
    Generic(width : natural := 2);
    Port(en_i : in std_logic;
         a_i : in std_logic_vector(width - 1 downto 0);
         b_o : out std_logic_vector(2 ** width - 1 downto 0));
end component;

-- MUX --
signal mux_o : std_logic;
signal mux_i : std_logic_vector(15 downto 0);
signal sel_i : std_logic_vector(3 downto 0);

-- D FF --
signal d_1, d_2, q_1, q_2 : std_logic;

-- DEC --
signal dec_in_1, dec_in_2 : std_logic_vector(1 downto 0);  

-- Second Circuit --
signal temp_1 : std_logic;

begin

-- Fist Circuit --

dec_in_1 <= f & e;
dec_in_2 <= h & g;
mux_i(15 downto 8) <= (others => '1');
d_1 <= mux_o;
o1 <= q_1;
o2 <= q_2;
sel_i <= d & c & b & a;

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

-- MUX --
mux_o <= mux_i(to_integer(unsigned(sel_i)));

-- DEC --
DEC_1: generic_dec
generic map(width => 2)
port map(a_i => dec_in_1, 
         en_i => '1',
         b_o => mux_i(3 downto 0));
         
DEC_2: generic_dec
generic map(width => 2)
port map(a_i => dec_in_2, 
         en_i => '1',
         b_o => mux_i(7 downto 4));

------------------

-- Second Circuit --

temp_1 <= ((not A) and (not B) and (not C) and (not E) and (not F)) or (A and (not B) and (not C) and E and (not F)) or
      ((not A) and B and (not C) and (not E) and F) or (A and B and (not C) and E and F) or
      ((not A) and (not B) and C and (not G) and (not H)) or (A and (not B) and C and G and (not H)) or
      ((not A) and B and C and (not G) and H) or (A and B and C and G and H);
d_2 <= (temp_1 and (not d)) or d;

------------------


end Behavioral;
