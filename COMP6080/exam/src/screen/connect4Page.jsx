import React, { useEffect } from 'react'
import { Box } from "@mui/material";
import BottomBar from "../components/bottomBar";
import { useWinContext, useWindowSizeContext } from "../context";

const Connect4Page = () => {
  const { width, height } = useWindowSizeContext();
  const { win, setWin } = useWinContext();
  const [board, setBoard] = React.useState(Array(10).fill(Array(10).fill(0)));
  const [currentPlayer, setCurrentPlayer] = React.useState(1);
  const [winner, setWinner] = React.useState(null);
  const [bg, setBg] = React.useState('#ccc');
  const [gameOver, setGameOver] = React.useState(0);
  const [total, setTotal] = React.useState(0);

  const click = (columnIndex) => {
    if (winner) return;
    const newBoard = board.map(row => [...row]);
    for (let i = 9; i >= 0; i--) {
      if (newBoard[i][columnIndex] === 0) {
        setTotal(total + 1)
        newBoard[i][columnIndex] = currentPlayer;
        setBoard(newBoard);
        setCurrentPlayer(currentPlayer === 1 ? 2 : 1);
        break;
      }
    }
  }

  useEffect(() => {
    setBoard(Array(10).fill(Array(10).fill(0)))
    setWinner(null);
    setTotal(0);
    setCurrentPlayer(1);
  }, []);

  useEffect(() => {
    const winner = checkWin();
    if (!winner && isBoardFull(board)) {
      setGameOver(0);
    } else if (winner) {
      setGameOver(winner);
    }
  }, [board]);

  const isBoardFull = (board) => board.every(row => row.every(cell => cell !== 0));

  const checkWin = () => {
    const boardSize = 10;
    const winningLength = 4;

    for (let row = 0; row < boardSize; row++) {
      for (let col = 0; col < boardSize - winningLength + 1; col++) {
        if (board[row][col] && board[row][col] === board[row][col + 1] && board[row][col] === board[row][col + 2] && board[row][col] === board[row][col + 3]) {
          return board[row][col];
        }
      }
    }

    for (let col = 0; col < boardSize; col++) {
      for (let row = 0; row < boardSize - winningLength + 1; row++) {
        if (board[row][col] && board[row][col] === board[row + 1][col] && board[row][col] === board[row + 2][col] && board[row][col] === board[row + 3][col]) {
          return board[row][col];
        }
      }
    }

    for (let row = 0; row < boardSize - winningLength + 1; row++) {
      for (let col = 0; col < boardSize - winningLength + 1; col++) {
        if (board[row][col] && board[row][col] === board[row + 1][col + 1] && board[row][col] === board[row + 2][col + 2] && board[row][col] === board[row + 3][col + 3]) {
          return board[row][col];
        }
      }
    }

    for (let row = 0; row < boardSize - winningLength + 1; row++) {
      for (let col = winningLength - 1; col < boardSize; col++) {
        if (board[row][col] && board[row][col] === board[row + 1][col - 1] && board[row][col] === board[row + 2][col - 2] && board[row][col] === board[row + 3][col - 3]) {
          return board[row][col];
        }
      }
    }

    return null;
  }

  useEffect(() => {
    let interval;
    if (gameOver) {
      let count = 0;
      interval = setInterval(() => {
        setBg(prevColor => prevColor === '#ccc' ? '#000' : '#ccc');
        count++;
        if (count >= 6) {
          clearInterval(interval);
          setTimeout(() => {
            setWinner(gameOver);
            if (gameOver === 1) {
              setWin(win + 1);
            }
          }, 500)
        }
      }, 500);
    }

    return () => {
      if (interval) {
        clearInterval(interval);
      }
    };
  }, [gameOver]);


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
      <Box sx={{
        width: winner && height <= 700 ? '200px' : '400px',
        height: winner && height <= 700 ? '200px' : '400px',
        display: 'flex',
        flexDirection: 'column',
        bgcolor: bg
      }}>
        {board.map((row, rowIndex) => (
          <Box key={rowIndex} sx={{ flex: 1, display: 'flex' }}>
            {row.map((cell, columnIndex) => (
              <Box
                key={`${rowIndex}-${columnIndex}`}
                sx={{ flex: 1, border: '2px solid #333' }}
              >
                <Box  onClick={() => click(columnIndex)} sx={{
                  backgroundColor: cell === 1 ? 'blue' : cell === 2 ? 'red' : 'transparent',
                  borderRadius: '50%',
                  height: '100%',
                  width : '100%'
                }}/>
              </Box>
            ))}
          </Box>
        ))}
      </Box>
      {winner && (
        <Box sx={{
          width: 400,
          height: 200,
          border: '1px solid #333',
          backgroundColor: '#fff',
          fontSize: '14pt',
          boxSizing: 'border-box',
          mt: 1
        }}>
          {`${winner === 0 ? 'No one wins' : `Player${winner} wins`}, A total of ${total} moves were made`}
        </Box>
      )}
      <BottomBar />
    </Box>
  );
}

export default Connect4Page;