context('Login flow', () => {
	beforeEach(() => {
		cy.visit('localhost:3000');
	});

	it('Successfully logs in after entering the correct credentials', () => {
		// Log in with the correct credentials
		const email = 'soorria@email.com';
		const password = 'super secure password';
		const welcomeText = "You're logged in!";

		cy.get('input[name=email]').focus().type(email);
		cy.get('input[name=password]').focus().type(password);
		cy.get('button[type=submit]').click();

		// Check that it is successful
		cy.get('h1').then((h1) => {
			expect(h1.text()).to.contain(welcomeText);
		});
	});
});