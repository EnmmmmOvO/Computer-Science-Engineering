import React, {useEffect, useState} from 'react'
import BottomBar from "../components/bottomBar";
import {Box, Button, Dialog, DialogActions, DialogContent, DialogContentText, DialogTitle} from "@mui/material";
import { useWindowSizeContext } from "../context";

const MemoryPage = () => {
  const { width, height } = useWindowSizeContext();
  const [start, setStart] = useState(false);
  const [open, setOpen] = useState(false);
  const [board, setBoard] = useState(Array(4).fill(Array(4).fill(0)));
  const [randomCells, setRandomCells] = useState([]);
  const [flash, setFlash] = React.useState([-1, -1]);

  const handleClose = () => setOpen(false);

  const randomFlash = (times) => {
    const result = [];
    for (let i = 0; i < times; i++) {
      const randomRow = Math.floor(Math.random() * 4);
      const randomCol = Math.floor(Math.random() * 4);
      result.push([randomRow, randomCol]);
    }
    setRandomCells(result);
  };

  useEffect(() => {
    if (start) {
      randomFlash(1);
    }
  }, [start]);

  useEffect(() => {
    flashStart(0, randomFlash.length);
  }, [randomCells]);

  const flashStart = (index, time) => {
    if (index === randomCells.length) setFlash([-1, -1]);
    setTimeout(() => {
      setFlash(randomCells[index])
      setTimeout(() => flashStart(index + 1, time), time);
    }, 500);
  }

  const handleCellClick = (rowIndex, columnIndex) => {
    // Add logic to handle cell click after flashing sequence
  };

  const handleStart = () => {
    setStart(true);
    setOpen(false);
  };

  return (
    <Box sx={{
      bgcolor: '#ccc',
      paddingBottom: width >= 1400 ? '100px' : width >= 800 ? '80px' : '60px',
      display: 'flex',
      flexDirection: 'column',
      alignItems: 'center',
      justifyContent: 'center',
      width: '100%',
      height: height - (width >= 1400 ? 100 : width >= 800 ? 80 : 60),
    }}>
      <Box sx={{ width: '400px', height: '400px', display: 'flex', flexDirection: 'column' }}>
        {board.map((row, rowIndex) => (
          <Box key={rowIndex} sx={{ flex: 1, display: 'flex' }}>
            {row.map((cell, columnIndex) => (
              <Box
                key={`${rowIndex}-${columnIndex}`}
                sx={{
                  flex: 1,
                  border: 'rgb(255,255,0) 1px solid',
                  bgcolor: 'white'
                }}
                onClick={() => handleCellClick(rowIndex, columnIndex)}
              />
            ))}
          </Box>
        ))}
      </Box>
      <Box>
        <Button variant="outlined" onClick={() => setOpen(true)} sx={{ mt: 2 }}>Reset</Button>
      </Box>

      <Dialog
        open={open}
        onClose={handleClose}
        aria-labelledby="alert-dialog-title"
        aria-describedby="alert-dialog-description"
      >
        <DialogTitle id="alert-dialog-title">
          {"Confirm"}
        </DialogTitle>
        <DialogContent>
          <DialogContentText id="alert-dialog-description">Would you like to play?</DialogContentText>
        </DialogContent>
        <DialogActions>
          <Button onClick={handleStart}>Yes</Button>
          <Button onClick={handleClose}>No</Button>
        </DialogActions>
      </Dialog>
      <BottomBar />
    </Box>
  )
}

export default MemoryPage;