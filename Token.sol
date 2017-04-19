pragma solidity ^0.4.9;
contract Token {
  mapping (address => uint) balance;
    function Token(uint n) {
        balance[msg.sender] = n;
    }
    function send(address a, uint amount) {
        if (balance[msg.sender] < amount) throw;
        balance[msg.sender] -= amount;
        balance[a] += amount;
    } 
}
