package banking;

import unsw.enrolment.Student;

import java.util.ArrayList;

public class LoggedBankAccount extends BankAccount {

    private ArrayList<CustomerAccount> customerAccountList;
    private ArrayList<Message> messageList;

    private final static int CREATE_ACCOUNT = 0,
            WITHDRAW = 1,
            DEPOSIT = 2;

    public LoggedBankAccount(int balance, String name) {
        super(balance, name);
        customerAccountList = new ArrayList<>();
        messageList = new ArrayList<>();
    }

    public void CreateAccount(String name) throws Exception {
        if (customerAccountList.stream().anyMatch(customerAccount -> customerAccount.getName().equals(name)))
            throw new Exception("Failure! The account with ths name is existed");
        CustomerAccount customerAccount = new CustomerAccount(name);
        customerAccountList.add(customerAccount);
        addMessage(new Message(customerAccount, CREATE_ACCOUNT), customerAccount);
    }

    public String getMessageList() {
        StringBuilder stringBuilder = new StringBuilder();
        messageList.stream().forEach(message -> stringBuilder.append(message.toString() +'\n'));
        return stringBuilder.toString();
    }

    public void DepositIntoAccount(int fund, String name) throws Exception {
        CustomerAccount customerAccount = null;

        for (CustomerAccount temp : customerAccountList) {
            if (temp.getName().equals(name)) {
                customerAccount = temp;
                break;
            }
        }

        if (customerAccount == null) throw new Exception ("Account with " + name + "is not existed");
        customerAccount.deposit(fund);
        deposit(fund);
        addMessage(new Message(customerAccount, DEPOSIT, fund), customerAccount);
    }

    public void WithdrawFromAccount(int fund, String name) throws Exception {
        CustomerAccount customerAccount = null;

        for (CustomerAccount temp : customerAccountList) {
            if (temp.getName().equals(name)) {
                customerAccount = temp;
                break;
            }
        }
        if (customerAccount == null) throw new Exception ("Account with " + name + "is not existed");

        try {
            customerAccount.withdraw(fund);
            withdraw(fund);
        } catch (BankBalanceException e) {
            customerAccount.deposit(fund);
            throw e;
        }
        addMessage(new Message(customerAccount, WITHDRAW, fund), customerAccount);
    }

    private void addMessage(Message m, CustomerAccount customerAccount) {
        customerAccount.addPersonalRecord(m);
        messageList.add(m);
    }

    public int getCustomerBalance(String name) throws Exception {
        CustomerAccount customerAccount = null;

        for (CustomerAccount temp : customerAccountList) {
            if (temp.getName().equals(name)) {
                customerAccount = temp;
                break;
            }
        }

        if (customerAccount == null) throw new Exception ("Account with " + name + "is not existed");
        return customerAccount.getBalance();
    }

}
