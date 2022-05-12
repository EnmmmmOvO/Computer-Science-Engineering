
income = int(input(print("Enter your income: "))

if income > 180000:
    tax = float(54232 + (float(income) - 180000) * 0.45)
elif income > 87000:
    tax = float(19822 + (float(income) - 87000) * 0.37)
elif income > 37000:
    tax = float(3572 + (float(income) - 37000) * 0.325)
elif income > 18200:
    tax = float((float(income) - 18200) * 0.325 * 0.01)
else:
    tax = 0

tax = '{:,.2f}'.format(tax)
print("The estimated tax on your income is " + "$" + tax)
