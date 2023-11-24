import React from 'react';

export const WindowContext = React.createContext(null);
export const useWindowContext = () => React.useContext(WindowContext);