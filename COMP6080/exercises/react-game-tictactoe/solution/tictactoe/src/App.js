import React, {useState} from 'react';
import './App.css';
import boardStyles from './board.module.css';

function App() {

  const defaultBoard =  [ [ '', '', '', ], 
                          [ '', '', '', ],
                          [ '', '', '', ], 
                        ];


  const [board, setBoard] = useState(defaultBoard); 
  const [player, setPlayer] = useState('X');
  const [winPlayer, setWinPlayer] = useState(''); 
  //In case of a win, stores indexes of winning row, column or diagonal 
  const [winningCells, setWinningCells] = useState([]); 
  
  //Handles cell clicks
  const handleClick = (rowNum, colNum) => {
    setCell(rowNum, colNum);
    checkWin();
  }
  
  //Checks if game has been won
  const checkWin = () => {
    const winningLines = [
      [[0, 0], [0, 1], [0, 2]],
      [[1, 0], [1, 1], [1, 2]],
      [[2, 0], [2, 1], [2, 2]],
      [[0, 0], [1, 0], [2, 0]],
      [[0, 1], [1, 1], [2, 1]],
      [[0, 2], [1, 2], [2, 2]],
      [[0, 0], [1, 1], [2, 2]],
      [[0, 2], [1, 1], [2, 0]],
    ]

    for (let line of winningLines) {
      const [a, b, c] = line;
      if (board[a[0]][a[1]] !== '' && board[a[0]][a[1]] === board[b[0]][b[1]] && board[b[0]][b[1]] === board[c[0]][c[1]]) {
        //Game won
        setWinPlayer(player === 'X' ? 'X' : 'O')
        setWinningCells([a, b, c])
        setWinCount(player);
      }
    }
  }

  //Handles local storage win counts
  const setWinCount = (winPlayer) => {
    if(winPlayer === 'X'){
      let winCount = localStorage.getItem("player_X_win_count");
      localStorage.setItem("player_X_win_count", winCount ? parseInt(winCount)+1 : 1);
    }else{
      let winCount = localStorage.getItem("player_O_win_count");
      localStorage.setItem("player_O_win_count", winCount ? parseInt(winCount)+1 : 1);
    }
  }
  
  //Change how the board looks when the player clicks on a cell
  const setCell = (x, y) => {
    const currPlayer = player;
    const newBoard = {...board}; //[ ... board ]
    console.log(newBoard);
    newBoard[x][y] = currPlayer; 

    setBoard(newBoard);
    setPlayer(player === 'X'? 'O': 'X');
  }

  const getCellStyle = (rowNum, colNum) => {
    if (winningCells.some(elem => elem[0] === rowNum && elem[1] === colNum)) {
      return boardStyles.winningCell;
    }
    return boardStyles.cell;
  }

  //Renders a 3x3 board 
  return (
    <div className="App">
      <div className={boardStyles.basicBoard}>
        {Array.from({length: 3}).map((row, rowNum)  => {
          return (
            <div className={boardStyles.row}> 
              {Array.from({length: 3}).map((cell, colNum) => {
                return (
                <div 
                  className={getCellStyle(rowNum, colNum)} 
                  onClick={() => handleClick(rowNum, colNum)}
                > 
                  {board[rowNum][colNum]}
                </div>
                )
              })}
            </div>)
        })}
        <p> Win player : {winPlayer}</p>
        </div>
    </div>
  );
}

export default App;
