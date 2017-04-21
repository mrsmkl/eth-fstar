pragma solidity ^0.4.10;

contract Pyramid {
    mapping (address => address) parent;
    mapping (address => uint) balance;
    mapping (address => address) invite;
    mapping (address => uint) invites_left;
    mapping (address => bool) joined;
    function calc(uint level) returns (uint) {
        return 10;
    }
    function doInvite(address addr) {
        if (invite[addr] != 0) throw;
        invite[addr] = msg.sender;
        invites_left[msg.sender]--;
    }
    function cancelInvite(address addr) {
        if (joined[addr] || invite[addr] != msg.sender) throw;
        invite[addr] = 0;
        invites_left[msg.sender]++;
    }
    function pull() {
        uint sum = balance[msg.sender];
        balance[msg.sender] = 0;
        msg.sender.transfer(sum);
    }
    function join() payable {
        if (msg.value < 1 ether) throw;
        if (joined[msg.sender]) throw;
        if (invite[msg.sender] != 0 && invites_left[invite[msg.sender]] > 0) {
            address par = invite[msg.sender];
            parent[msg.sender] = par;
            joined[msg.sender] = true;
            invites_left[msg.sender] = 3;
            for (uint256 i = 0; i < 10; i++) {
                balance[par] += calc(i);
                par = parent[par];
            }
        }
    }
}
