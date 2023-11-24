import React from 'react'


export const WindowSizeContext = React.createContext(null);
export const useWindowSizeContext = () => React.useContext(WindowSizeContext);

export const WinContext = React.createContext(null);
export const useWinContext = () => React.useContext(WinContext);