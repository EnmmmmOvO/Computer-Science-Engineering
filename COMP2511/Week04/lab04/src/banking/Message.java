package banking;

import java.text.SimpleDateFormat;
import java.util.Date;

public class Message {
    private CustomerAccount customerAccount;
    private final static int CREATE_ACCOUNT = 0,
                             WITHDRAW = 1,
                             DEPOSIT = 2;

    private int status;
    private int value;

    public Message(CustomerAccount customerAccount, int status) {
        this.status = status;
        value = 0;
        this.customerAccount = customerAccount;
    }

    public Message(CustomerAccount customerAccount, int status, int value) {
        this.status = status;
        this.value = value;
        this.customerAccount = customerAccount;
    }

    @Override
    public String toString() {
        switch (status) {
            case CREATE_ACCOUNT: return customerAccount.getName() + " Create an account";
            case WITHDRAW: return customerAccount.getName() + " Withdraw $" + value + " from his/her account";
            case DEPOSIT: return customerAccount.getName() + " Deposit $" + value + " into his/her account";
        }
        return null;
    }
}
