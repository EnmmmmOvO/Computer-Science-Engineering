import React from "react";
import { ProductCard } from "./ProductCard";
import { Cart } from "./Cart";
import bike1 from "./images/bike1.jpg";
import bike2 from "./images/bike2.jpg";
import bike3 from "./images/bike3.jpg";
import {Routes, Route} from "react-router";

// All of the bikes available
const items = [
  {
    id: "glow-in-the-dark-bike-1",
    image: bike1,
    title: "Glow in the dark bike 1",
    price: 10,
    currency: "AUD",
    descriptions: [
      "Have no more fear during your nightly bike rights, our latest glow-in-the-dark model ensures maximum visibility for maximum safety.",
      "More colours coming soon in 2021.",
    ],
    recommendationRatio: 0.25,
  },
  {
    id: "glow-in-the-dark-bike-2",
    image: bike2,
    title: "Glow in the dark bike 2",
    price: 20,
    currency: "AUD",
    descriptions: [
      "Have no more fear during your nightly bike rights, our latest glow-in-the-dark model ensures maximum visibility for maximum safety.",
      "More colours coming soon in 2021.",
    ],
    recommendationRatio: 0.5,
  },
  {
    id: "glow-in-the-dark-bike-3",
    image: bike3,
    title: "Glow in the dark bike 3",
    price: 50,
    currency: "AUD",
    descriptions: [
      "Have no more fear during your nightly bike rights, our latest glow-in-the-dark model ensures maximum visibility for maximum safety.",
      "More colours coming soon in 2021.",
    ],
    recommendationRatio: 0.75,
  },
];

function App() {
  return (
    <Routes>
      <Route exact path="/" element={<ProductCard
          item={items[2]}
          onAddToCart={(id, quantity) => {
            // TODO
            console.log(`${id}: ${quantity}`);
          }}
      />}>
        {/* Render the ProductCard for the "/" path */}
        {/* TODO - add another <Route> that renders the <Cart/> component */}
      </Route>
    </Routes>
  );
}

export default App;
