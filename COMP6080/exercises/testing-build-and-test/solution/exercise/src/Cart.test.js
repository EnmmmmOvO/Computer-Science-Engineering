import React from "react";
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { Cart } from "./Cart";

describe("Cart component", () => {
  const items = {
    "Glow in the dark bike 3": 10,
  };

  it("displays the title of an item in the cart", () => {
    render(<Cart items={items} onRemoveFromCart={() => {}} />);
    expect(screen.getByText(/glow in the dark bike 3/i)).toBeInTheDocument();
  });

  it("displays the quantity of an item in the cart", () => {
    render(<Cart items={items} onRemoveFromCart={() => {}} />);
    expect(screen.getByText(/10/i)).toBeInTheDocument();
  });

  it("removes an item from the cart", () => {
    const onRemoveFromCart = jest.fn(); 
    render(<Cart items={items} onRemoveFromCart={onRemoveFromCart} />);
    userEvent.click(screen.getByRole('button', { name: /remove item/i }));
    expect(onRemoveFromCart).toHaveBeenCalledWith("Glow in the dark bike 3")
  });
});
