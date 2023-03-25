package banking;

import java.util.ArrayList;

public class CustomerAccount {
    private String name;
    private int balance;

    private ArrayList<Message> personalRecord;

    public CustomerAccount(String name) {
        this.name = name;
        this.balance = 0;
        personalRecord = new ArrayList<>();
    }

    public void addPersonalRecord(Message m) {
        personalRecord.add(m);
    }

    public int getBalance() {
        return balance;
    }

    public String getName() {
        return name;
    }

    public void deposit(int fund) {
        balance += fund;
    }

    public void withdraw(int fund) throws Exception {
        if (balance < fund) throw new Exception("There are not enough money in " +  name + "'s account");
        balance -= fund;
    }

    public ArrayList<Message> getPersonalRecord() {
        return personalRecord;
    }

}
