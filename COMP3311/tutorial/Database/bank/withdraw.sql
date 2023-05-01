--
-- Withdrawal functions on the Banks database
-- All check that sufficient funds are available
--

-- First version of "withdraw" function
-- First version of the withdraw(cust/acct,amount) function
-- Assumes that the account exists
-- Assumes that each customer has only one account

create or replace function
	withdraw(_person text, _amount real) returns text
as $$
declare
	_current real;  _newbalance real;
begin
	select into _current balance
	from   Accounts
	where  holder = _person;
	if (_amount > _current) then
		return 'Insufficient Funds';
	else
		_newbalance := _current - _amount;
		update Accounts
		set    balance = _newbalance
		where  holder = _person;
		return 'New Balance: '||_newbalance;
	end if;
end;
$$ language plpgsql;


-- Second version of the withdraw(cust/acct,amount) function
-- Check for valid customer
-- Assumes each customer has only one account

create or replace function
	withdraw1(_person text, _amount real) returns text
as $$
declare
	_current real;  _newbalance real;  _n text;
begin
	select into _n name
	from   Customers
	where  name = _person;
	if not found then
		return 'Unknown customer';
	end if;
	select into _current balance
	from   Accounts
	where  holder = _person;
	if (_amount > _current) then
		return 'Insufficient Funds';
	else
		_newbalance := _current - _amount;
		update Accounts
		set    balance = _newbalance
		where  holder = _person;
		return 'New Balance: '||_newbalance;
	end if;
end;
$$ language plpgsql;


-- Third version of the withdraw(cust/acct,amount) function
-- Check for valid customer, and check for multiple accounts

create or replace function
	withdraw2(_person text, _amount real) returns text
as $$
declare
	_current real;  _newbalance real;
	_n text;  _naccts integer;
begin
	select into _n name
	from   Customers
	where  name = _person;
	if not found then
		return 'Unknown customer';
	end if;
	select into _naccts count(*)
	from   Accounts
	where  holder = _person;
	if (_naccts = 0) then
		return 'Customer has no accounts';
	elsif (_naccts > 1) then
		return 'Customer has several accounts';
	end if;
	select into _current balance
	from   Accounts
	where  holder = _person;
	if (_amount > _current) then
		return 'Insufficient Funds';
	else
		_newbalance := _current - _amount;
		update Accounts
		set    balance = _newbalance
		where  holder = _person;
		return 'New Balance: '||_newbalance;
	end if;
end;
$$ language plpgsql;


