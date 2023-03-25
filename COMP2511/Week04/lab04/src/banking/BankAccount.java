package banking;


public abstract class BankAccount {

    private int balance;
    private String name;

    public BankAccount(int balance, String name) {
        this.balance = balance;
        this.name = name;
    }

    public void deposit(int fund) {
        balance += fund;
    }

    public void withdraw(int fund) throws Exception {
        if (balance < fund) throw new BankBalanceException("Do not have enough money");
        balance -= fund;
    }

    public int getBalance() {
        return balance;
    }

    public void testBalance(int balance) {
        this.balance -= balance;
    }
}