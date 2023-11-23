import {React, useEffect, useState} from "react";

import './App.css';

function App() {
  const [table, setTable] = useState([[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
  const [score, setScore] = useState(0);
  const [maxScore, setMaxScore] = useState(localStorage.getItem('2048-Best') || 0);
  const [start, setStart] = useState(false);

  const startGame = () => {
    const new_table = table.slice();
    setRandomCell(new_table);
    setTable(new_table);
    setStart(true);
  }

  const reset = () => {
    setTable([[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]);
    setScore(0);
    setStart(false);
  };

  const setRandomCell = (next_table) => {
    const getRandomInt = (max) => Math.floor(Math.random() * Math.ceil(max))
    const empty = [];
    let finish = false;
    next_table.forEach((row, rowIndex) => {
      row.forEach((cell, colIndex) => {
        if (cell === 0) empty.push([rowIndex, colIndex]);
        else if (cell === 2048) finish = true;
      });
    });

    if (finish) return 1;
    if (empty.length === 0) return 0;

    for (let i = start ? 1 : 2; i > 0; i--) {
       let position = empty.splice(getRandomInt(empty.length), 1);
       next_table[position[0][0]][position[0][1]] = 2;
    }

    return -1;
  }

  const moveLeft = (next_table) => {
    let change = false;
    let score = 0;
    for (let i = 3; i >= 0; i--) {
      for (let j = 1; j < 4; j++) {
        if (next_table[i][j] !== 0) {
          let check = true;
          for (let k = 0; k < j; k++) {
            if (next_table[i][k] === 0) {
              change = true;
              if (k > 0 && next_table[i][j] === next_table[i][k - 1]) {
                next_table[i][k - 1] *= 2;
                score += next_table[i][k - 1];
              } else next_table[i][k] = next_table[i][j];
              next_table[i][j] = 0;
              check = false;
              break
            }
          }

          if (check && j > 0 && next_table[i][j] === next_table[i][j - 1]) {
            next_table[i][j - 1] *= 2;
            change = true;
            score += next_table[i][j - 1];
            next_table[i][j] = 0;
          }
        }
      }
    }
    return [change, score];
  }

  const moveRight = (next_table) => {
    let change = false;
    let score = 0;
    for (let i = 0; i < 4; i++) {
      for (let j = 2; j >= 0; j--) {
        if (next_table[i][j] !== 0) {
          let check = true;
          for (let k = 3; k > j; k--) {
            if (next_table[i][k] === 0) {
              change = true;
              if (k < 3 && next_table[i][j] === next_table[i][k + 1]) {
                next_table[i][k + 1] *= 2;
                score += next_table[i][k + 1];
              } else next_table[i][k] = next_table[i][j];
              next_table[i][j] = 0;
              check = false;
              break
            }
          }

          if (check && j < 3 && next_table[i][j] === next_table[i][j + 1]) {
            next_table[i][j + 1] *= 2;
            score += next_table[i][j + 1];
            change = true;
            next_table[i][j] = 0;
          }
        }
      }
    }
    return [change, score];
  }

  const moveDown = (next_table) => {
    let change = false;
    let score = 0;
    for (let i = 0; i < 4; i++) {
      for (let j = 2; j >= 0; j--) {
        if (next_table[j][i] !== 0) {
          let check = true;
          for (let k = 3; k > j; k--) {
            if (next_table[k][i] === 0) {
              change = true;
              if (k < 3 && next_table[j][i] === next_table[k + 1][i]) {
                next_table[k + 1][i] *= 2;
                score += next_table[k + 1][i];
              } else next_table[k][i] = next_table[j][i];
              next_table[j][i] = 0;
              check = false;
              break
            }
          }

          if (check && j < 3 && next_table[j][i] === next_table[j + 1][i]) {
            next_table[j + 1][i] *= 2;
            score += next_table[j + 1][i];
            change = true;
            next_table[j][i] = 0;
          }
        }
      }
    }
    return [change, score];
  }

  const moveUp = (next_table) => {
    let change = false;
    let score = 0;
    for (let i = 3; i >= 0; i--) {
      for (let j = 1; j < 4; j++) {
        if (next_table[j][i] !== 0) {
          let check = true;
          for (let k = 0; k < j; k++) {
            if (next_table[k][i] === 0) {
              change = true;
              if (k > 0 && next_table[j][i] === next_table[k - 1][i]) {
                next_table[k - 1][i] *= 2;
                score += next_table[k - 1][i];
              } else next_table[k][i] = next_table[j][i];
              next_table[j][i] = 0;
              check = false;
              break
            }
          }

          if (check && j > 0 && next_table[j][i] === next_table[j - 1][i]) {
            next_table[j - 1][i] *= 2;
            score += next_table[j - 1][i]
            change = true;
            next_table[j][i] = 0;
          }
        }
      }
    }
    return [change, score];
  }

  const keyDownStep = (event) => {
    let next_table = table.slice();
    let moveResult = [];

    switch (event.key) {
      case 'w': case 'ArrowUp': moveResult = moveUp(next_table); break;
      case 's': case 'ArrowDown': moveResult = moveDown(next_table); break;
      case 'a': case 'ArrowLeft': moveResult = moveLeft(next_table); break;
      case 'd': case 'ArrowRight': moveResult = moveRight(next_table); break;
      default: return;
    }

    setScore(score + moveResult[1])

    const result = setRandomCell(next_table);
    console.log(result);
    setTable(next_table);

    if (result === 1) {
      window.alert('U win!');
    } if (result === 0 && !checkEnd(next_table)) {
      window.alert('Game Over')
    }
  }

  useEffect(() => {
    if (score > maxScore) {
      setMaxScore(score)
      localStorage.setItem('2048-Best', score.toString());
    }
  }, [maxScore, score])

  const checkEnd = (next_table) => {
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        if (next_table[i][j] === next_table[i][j + 1] || next_table[i][j] === next_table[i + 1][j]) return true
      }
    }
    return false;
  }


  return (
    <div className="App" tabIndex="0" onKeyDown={start ? keyDownStep : undefined}>
      <div className={"score"}><div>Score: {score}</div> <div>Best: {maxScore}</div></div>
      <table className={"box"}>
        <tbody className={"table"}>
          {table.map((row, rowIndex) => {
            return (
                <tr className={"tr"} key={rowIndex}>
                  {row.map((cell, colIndex) => {
                    return <td className={`cell cell-${table[rowIndex][colIndex]}`} key={colIndex}>
                        {table[rowIndex][colIndex] === 0 ? '' : table[rowIndex][colIndex]}
                    </td>;
                  })}
                </tr>
            )
          })}
        </tbody>
      </table>
      <div className={"button-box"}>
        <button onClick={start ? undefined : startGame}>Start</button>
        <button onClick={reset}>Reset</button>
      </div>
    </div>
  );
}

export default App;
