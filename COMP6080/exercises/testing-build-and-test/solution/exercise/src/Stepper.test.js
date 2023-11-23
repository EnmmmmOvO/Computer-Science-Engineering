import React from "react";
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

import { Stepper } from "./Stepper";

describe("Stepper component", () => {
  it("displays the correct value", () => {
    render(<Stepper value={3} onUpdate={() => {}} />);
    expect(screen.getByText(/3/i)).toBeInTheDocument();
  });

  it("decrements the value", () => {
    const onUpdate = jest.fn();
    render(<Stepper value={3} onUpdate={onUpdate} />);
    userEvent.click(screen.getByLabelText(/subtract 1 from quantity/i));
    expect(onUpdate).toHaveBeenCalledWith(2);
  });

  it("increments the value", () => {
    const onUpdate = jest.fn();
    render(<Stepper value={3} onUpdate={onUpdate} />);
    userEvent.click(screen.getByLabelText(/add 1 to quantity/i));
    expect(onUpdate).toHaveBeenCalledWith(4);
  });
});
