context('Count down from 10 to launch', () => {
	beforeEach(() => {
		cy.visit('localhost:3000');
	});

	it('Successfully logs in after entering the correct credentials', () => {
		// Check the timer starts from 10
		cy.get('#timer').then((timer) => {
			expect(timer.text()).to.contain(10);
		});

		// Start the countdown
		cy.get('#start').click();

		// Check the button is disabled before the countdown ends
		cy.get('#start').should('be.disabled');

		// Wait for 10 seconds
		cy.wait(10000);

		cy.get('#timer').then((timer) => {
			expect(timer.text()).to.contain('Launch!');
		});
	});
});