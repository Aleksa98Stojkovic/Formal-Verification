library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity Circuit_v1_p1 is
     port(
         rst : in std_logic;
         clk : in std_logic;
         a : in std_logic;
         b : in std_logic;
         c : in std_logic;
         d : in std_logic;
         e : in std_logic;
         f : in std_logic;
         o1 : out std_logic;
         o2 : out std_logic
     );

end Circuit_v1_p1;

architecture Behavioral of Circuit_v1_p1 is

 signal sel : std_logic_vector(3 downto 0);
 signal o1_reg, o1_next : std_logic;
 signal o2_reg, o2_next : std_logic;


begin

reg_proc : process(clk, rst)
 begin
     if (rst = '1') then
         o1_reg <= '0';
         o2_reg <= '0';
     elsif rising_edge(clk) then
         o1_reg <= o1_next;
         o2_reg <= o2_next;
     end if;
end process reg_proc;

o1 <= o1_reg;
o2 <= o2_reg;
o1_next <= (a and (not b) and c) or (a and (not d)) or 
(b and c and d) or (e and f);

with sel select
 
    o2_next <= a when "0000",
               a when "0001",
               a when "0010",
               a when "0011",
              '0' when "0100",
              '0' when "0101",
               a when "0110",
              '1' when "0111",
              (a or f) when "1000",
              (a or f) when "1001",
              (a or f) when "1010",
              (a or f) when "1011",
               f when "1100",
               f when "1101",
              (a or f) when "1110",
              '1' when others;
              
sel <= e & d & c & b;

end Behavioral;
