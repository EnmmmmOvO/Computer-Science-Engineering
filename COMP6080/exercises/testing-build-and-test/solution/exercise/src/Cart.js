import * as React from "react";
import { useNavigate } from "react-router-dom";

export const Cart = ({ items, onRemoveFromCart }) => {
  let history = useNavigate();

  const cartItems = [];
  for (const [title, quantity] of Object.entries(items)) {
    cartItems.push(
      <tr key={title}>
        <td>
          <p className="cart-title">{title}</p>
          <br />
          <button
            className="remove cart-button"
            onClick={() => onRemoveFromCart(title)}
          >
            Remove item
          </button>
        </td>
        <td>
          <p className="cart-quantity">{quantity}</p>
        </td>
      </tr>
    );
  }

  return (
    <div className="cart">
      <div>
        <h1>My Cart</h1>
        <table className="cart-table">
          <thead>
            <tr>
              <th>Title</th>
              <th>Quantity</th>
            </tr>
          </thead>
          <tbody>{cartItems}</tbody>
        </table>
        <button
          className="cart-button"
          onClick={() => {
            history("/");
          }}
        >
          Go Back
        </button>
      </div>
    </div>
  );
};
