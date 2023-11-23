import React from "react";
import { useNavigate } from "react-router-dom";
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
  let history = useNavigate();
  const [cartItems, setCartItems] = React.useState({});

  // Add an item to the cartItems state
  const addCartItem = (id, quantity) => {
    // Search for the title of the item
    let title = "";
    for (const item of items) {
      if (item.id === id) {
        title = item.title;
        break;
      }
    }

    // Update the cart
    if (cartItems[title]) {
      setCartItems({
        ...cartItems,
        [title]: cartItems[title] + quantity,
      });
    } else {
      setCartItems({
        ...cartItems,
        [title]: quantity,
      });
    }
  };

  // Remove an item from the cartItems state
  const removeCartItem = (title) => {
    setCartItems(
      Object.assign(
        {},
        Object.keys(cartItems).filter((t) => t !== title)
      )
    );
  };

  return (
    <Routes>
      <Route exact path="/" element=
          {<ProductCard
          item={items[2]}
          onAddToCart={(id, quantity) => {
            if (quantity > 0) {
              history("/cart");
              addCartItem(id, quantity);
            }
          }}/>}
      >
        {/* Render the ProductCard for the "/" path */}

      </Route>
      <Route path="/cart" element={<Cart
          items={cartItems}
          onRemoveFromCart={(title) => {
            removeCartItem(title);
          }}/>}
      >
        {/* Render the cart for the "/cart" path */}
      </Route>
    </Routes>
  );
}

export default App;
