import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import * as React from 'react';
import { Menu, MenuButton, MenuItem } from './Menu';

describe('MenuButton', () => {
  const noop = () => {};

  it('triggers onClick event handler when clicked', () => {
    const onClick = jest.fn();
    render(<MenuButton onClick={onClick} open={false} />);
    userEvent.click(screen.getByRole('button'));
    expect(onClick).toBeCalledTimes(1);
  });

  it('has an aria-label attribute', () => {
    render(<MenuButton onClick={noop} open={false} />);
    expect(screen.getByRole('button')).toHaveAttribute('aria-label');
  });

  it('sets aria-expanded to false when closed', () => {
    render(<MenuButton onClick={noop} open={false} />);
    expect(screen.getByRole('button')).toHaveAttribute('aria-expanded', 'false');
  });

  it('sets aria-expanded to true when open', () => {
    render(<MenuButton onClick={noop} open={true} />);
    expect(screen.getByRole('button')).toHaveAttribute('aria-expanded', 'true');
  });
});

describe('MenuItem', () => {
  const noop = () => {};

  it('triggers onClick event handler with title when clicked', () => {
    const onClick = jest.fn();
    render(<MenuItem onClick={onClick} title={'A title'} />);
    userEvent.click(screen.getByRole('link'));
    expect(onClick).toBeCalledWith('A title');
  });

  it('renders with custom title', () => {
    const title = 'My custom title';
    render(<MenuItem onClick={noop} title={title} />);
    expect(screen.getByRole('link')).toHaveTextContent(title);
  })
});

describe('Menu', () => {
  const noop = () => {};
  const items = ['Item 1', 'Item 2', 'Item 3'];

  it('is closed by default', () => {
    render(<Menu onClick={noop} items={items} />);
    expect(screen.getByRole('button')).toBeInTheDocument();
    expect(screen.queryByRole('link')).not.toBeInTheDocument();
  });

  it('creates a MenuItem for every provided item', () => {
    render(<Menu onClick={noop} items={items} />);
    expect(screen.queryByRole('link')).not.toBeInTheDocument();
    userEvent.click(screen.getByRole('button'))
    expect(screen.getAllByRole('link')).toHaveLength(3);
  });
});
