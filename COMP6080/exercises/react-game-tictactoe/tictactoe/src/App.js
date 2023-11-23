import React, {useCallback, useEffect, useState} from 'react'
import './App.css';
import {Button} from "@mui/material";

function App() {
    const [arr, setArr] = useState([['', '', ''], ['', '', ''], ['', '', '']])
    const [player, setPlayer] = useState(true);
    const [title, setTitle] = useState('');
    const [end, setEnd] = useState(false);
    const [winingCell, setWinningCell] = useState([])



    const clickBox = (row, col) => {
        if (end) window.alert('Game over, Click reset button to next game')
        else {
            if (arr[row][col] === '') sign(row, col);
            else window.alert('There are already pieces here.');
        }
    }


    const checkWin = useCallback(() => {
        const check = (a, b, c) => a !== '' && a === b && b === c

        for (let i = 0; i < 3; ++i) {
            if (check(arr[0][i], arr[1][i], arr[2][i])) {
                setWinningCell([[0, i], [1, i], [2, i]])
                return 1;
            }
            if (check(arr[i][0], arr[i][1], arr[i][2])) {
                setWinningCell([[i, 0], [i, 1], [i, 2]])
                return 1;
            }
        }

        if (check(arr[0][0], arr[1][1], arr[2][2])) {
            setWinningCell([[0, 0], [1, 1], [2, 2]])
            return 1;
        }
        if (check(arr[0][2], arr[1][1], arr[2][0])) {
            setWinningCell([[2, 0], [1, 1], [0, 2]])
            return 1;
        }
        if (arr.every(line => line.every(cell => cell !== ''))) return -1;

        return 0;
    }, [arr]);

    useEffect(() => {
        switch (checkWin()) {
            case 1:
                setEnd(true);
                setTitle(`${!player ? '✓' : '○'} Win`);
                break;
            case -1:
                setEnd(true);
                setTitle(`Tie`);
                break;
            default: break;
        }
    }, [arr, checkWin, player]);

    const sign = (row, col) => {
        setArr(arr.map((rowArr, rowIndex) => {
            return rowArr.map((cell, colIndex) =>
                row === rowIndex && col === colIndex ? player ? '✓' : '○' : cell
            )
        }));
        setPlayer(!player)
    };

    return (
        <div className="App">
            <div className="result" id="result">{title}</div>
            <div className="Container">
                {arr.map((rowArr, rowIndex) => (
                    <div className="Row-Container" key={rowIndex}>
                        {rowArr.map((cell, colIndex) => (
                            <div
                                className={`Box ${winingCell.some(sub => 
                                    sub[0] === rowIndex && sub[1] === colIndex
                                ) ? 'Correct' : ''}`}
                                key={colIndex} onClick={() => clickBox(rowIndex, colIndex)}
                            >{cell}</div>
                        ))}
                    </div>
                ))}
            </div>
            <Button
                variant="contained"
                onClick={() => {
                    setArr([['', '', ''], ['', '', ''], ['', '', '']]);
                    setEnd(false);
                    setTitle('')
                    setWinningCell([])
                }}
            >Reset</Button>
        </div>
    );
}

export default App;
