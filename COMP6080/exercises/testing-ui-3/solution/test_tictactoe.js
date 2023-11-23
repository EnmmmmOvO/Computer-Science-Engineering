context('Tictactoe', () => {
	beforeEach(() => {
		cy.visit('localhost:3000');
	});

	it('Starts with all empty cells and no win player displayed', () => {
		cy.get('#result').then((result) => {
			expect(result.text()).to.contain('Win player :');
		});

		for (let index = 0; index < 9; ++index) {
			cy.get(`#${index}`).then((cell) => {
				expect(cell.text()).to.contain('');
			});
		}
	});

	it('Does not allow the player to play at the cell that has already been played previously', () => {
		cy.get('#0').then((cell) => {
			expect(cell.text()).to.contain('');
		});

		cy.get('#0').click();
		cy.get('#0').then((cell) => {
			expect(cell.text()).to.contain('X');
		});

		cy.get('#0').click();
		cy.get('#0').then((cell) => {
			expect(cell.text()).to.contain('X');
		});
	});

	it('Changes board state when X wins diagonally', () => {
		// Play X to win diagonally
		cy.get('#0').click();
		cy.get('#1').click();
		cy.get('#4').click();
		cy.get('#5').click();
		cy.get('#8').click();

		cy.get('#result').then((result) => {
			expect(result.text()).to.contain('Win player : X');
		});

		// Winning cells should have a limegreen background colour and the rest don't
		for (let index = 0; index < 9; ++index) {
			const cell = cy.get(`#${index}`);
			if ([0, 4, 8].includes(index)) {
				cell.should('have.css', 'background-color', 'rgb(50, 205, 50)');
				cell.then((cell) => {
					expect(cell.text()).to.contain('X');
				});
			} else {
				cell.should('have.css', 'background-color', 'rgba(0, 0, 0, 0)');
			}
		}

		// Clicking another cell does not change the game after it has been won
		cy.get('#0').click();
		cy.get('#0').then((cell) => {
			expect(cell.text()).to.contain('X');
		});

		cy.get('#2').click();
		cy.get('#2').then((cell) => {
			expect(cell.text()).to.contain('');
		});
	});
});