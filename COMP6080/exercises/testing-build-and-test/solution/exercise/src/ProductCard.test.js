import React from "react";
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

import { ProductCard } from "./ProductCard";
import bike3 from "./images/bike3.jpg";

const testItem = {
  id: "glow-in-the-dark-bike",
  image: bike3,
  title: "Glow in the dark bike 3",
  price: 50,
  currency: "AUD",
  descriptions: [
    "Have no more fear during your nightly bike rights, our latest glow-in-the-dark model ensures maximum visibility for maximum safety.",
    "More colours coming soon in 2021.",
  ],
  recommendationRatio: 0.75,
};

describe("ProductCard component", () => {
  it("displays an image with an alt tag", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} />);
    expect(screen.getByRole('img', { name: /glow in the dark bike 3/i })).toBeInTheDocument();
  });

  it("displays a title", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} />);
    expect(screen.getByRole('heading', { name: /glow in the dark bike 3/i })).toBeInTheDocument();
  });

  it("displays a price with a currency", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} />);
    expect(screen.getByText(/\$50\.00 aud/i)).toBeInTheDocument();
  });

  it("displays a discounted price with a currency", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} discount={0.2} />);
    expect(screen.getByText(/\$40\.00 aud/i)).toBeInTheDocument();
  });

  it("displays all descriptions", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} />);
    expect(screen.getByText(/have no more fear during your nightly bike rights, our latest glow-in-the-dark model ensures maximum visibility for maximum safety\./i)).toBeInTheDocument()
    expect(screen.getByText(/more colours coming soon in 2021\./i)).toBeInTheDocument()
  });

  it("displays a rating text", () => {
    render(<ProductCard item={testItem} onAddToCart={() => {}} />);
    expect(screen.getByText(/highly recommended by 75% users/i)).toBeInTheDocument()
  });

  it("updates the quantity", () => {
    const onAddToCart = jest.fn();
    render(<ProductCard item={testItem} onAddToCart={onAddToCart} />);
    userEvent.click(screen.getByLabelText(/add 1 to quantity/i));
    userEvent.click(screen.getByRole('button', { name: /add to cart/i }));
    expect(onAddToCart).toHaveBeenCalledWith(testItem.id, 1)
  });
});
