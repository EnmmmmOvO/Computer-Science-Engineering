package banking;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertThrows;

public class BankTest {

    @Test
    public void createBank() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertEquals(10000, bank.getBalance());
    }

    @Test
    public void addCustomer() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertDoesNotThrow(() -> {
            bank.CreateAccount("William");
            assertEquals(bank.getMessageList(), "William Create an account\n");
        });
    }

    @Test
    public void addSameCustomer() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertThrows(Exception.class, () -> {
            bank.CreateAccount("William");
            bank.CreateAccount("William");
        });
    }

    @Test
    public void deposit() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertDoesNotThrow(() -> {
            bank.CreateAccount("William");
            bank.DepositIntoAccount(10000, "William");
            assertEquals(20000, bank.getBalance());
            assertEquals(10000, bank.getCustomerBalance("William"));
            assertEquals(bank.getMessageList(), "William Create an account\n" +
                    "William Deposit $10000 into his/her account\n");
        });
    }

    @Test
    public void depositNoCustomer() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertThrows(Exception.class, () -> {
            bank.CreateAccount("William");
            bank.DepositIntoAccount(10000, "Jack");
        });
    }

    @Test
    public void withdraw() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertDoesNotThrow(() -> {
            bank.CreateAccount("William");
            bank.DepositIntoAccount(10000, "William");
            bank.WithdrawFromAccount(10000, "William");
            assertEquals(bank.getMessageList(), "William Create an account\n" +
                            "William Deposit $10000 into his/her account\n" +
                    "William Withdraw $10000 from his/her account\n");
            assertEquals(10000, bank.getBalance());
            assertEquals(0, bank.getCustomerBalance("William"));

        });
    }

    @Test
    public void withdrawAccountNotEnoughBalance() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertThrows(Exception.class, () -> {
            bank.CreateAccount("William");
            bank.WithdrawFromAccount(10000,"William");
        });
    }

    @Test
    public void withdrawBankNotEnoughBalance() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertDoesNotThrow(() -> {
            bank.CreateAccount("William");
            bank.DepositIntoAccount(10000, "William");
            bank.testBalance(15000);
            assertThrows(BankBalanceException.class, () -> {
                bank.WithdrawFromAccount(10000, "William");
            });
            assertEquals(10000, bank.getCustomerBalance("William"));
        });
    }

    @Test
    public void testRecord() {
        LoggedBankAccount bank = new LoggedBankAccount(10000, "CommonWealth");
        assertDoesNotThrow(() -> {
            bank.CreateAccount("William");
            bank.DepositIntoAccount(10000, "William");
            bank.CreateAccount("Jack");
            bank.DepositIntoAccount(2000, "Jack");
            bank.WithdrawFromAccount(250, "William");
            bank.CreateAccount("Xavier");
            bank.DepositIntoAccount(100, "Xavier");
            bank.WithdrawFromAccount(2, "Xavier");
            bank.WithdrawFromAccount(2000, "William");
            String temp = "William Create an account\n" +
                    "William Deposit $10000 into his/her account\n" +
                    "Jack Create an account\n" +
                    "Jack Deposit $2000 into his/her account\n" +
                    "William Withdraw $250 from his/her account\n" +
                    "Xavier Create an account\n" +
                    "Xavier Deposit $100 into his/her account\n" +
                    "Xavier Withdraw $2 from his/her account\n" +
                    "William Withdraw $2000 from his/her account\n";
            assertEquals(temp, bank.getMessageList());
        });
    }
}
