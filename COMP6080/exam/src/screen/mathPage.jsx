import React, {useEffect} from 'react';
import {useWinContext, useWindowSizeContext} from "../context";
import {Box, Button, styled, TextField} from "@mui/material";
import BottomBar from "../components/bottomBar";

const MathPage = () => {
  const { win, setWin } = useWinContext();
  const { width, height } = useWindowSizeContext();
  const [result, setResult] = React.useState(0);
  const [first, setFirst] = React.useState(0);
  const [second, setSecond] = React.useState(0);
  const [operator, setOperator] = React.useState(0);

  const CustomerBox = styled(Box)({
    height: '40%',
    width: '20%',
    background: 'linear-gradient(to right, #abcabc, #cbacbd)',
    display: 'flex',
    justifyContent: 'center',
    alignItems: 'center',
    fontSize: 40,
  });

  const random = () => {
    setFirst(Math.floor(Math.random() * 50) + 1);
    setSecond(Math.floor(Math.random() * 50) + 1);
    setOperator(Math.floor(Math.random() * 5));
  }

  useEffect(() => {
    random();
  }, []);

  useEffect(() => {
    switch (operator) {
      case 0:
        setResult(first + second);
        break;
      case 1:
        setResult(first - second);
        break;
      case 2:
        setResult(first * second);
        break;
      case 3: {
        const r = first / second;
        setResult(!Number.isInteger(r) ? r.toFixed(1) : r);
        break;
      }
      case 4: {
        setResult(first % second)
        break;
      }
      default:
        break;
    }
  }, [first, second, operator]);

  const checkResult = (event) => {
    if (event.target.value === result.toString()) {
      setTimeout(() => {
        window.alert(`Congratulations`);
        setWin(win + 1);
        random();
      }, 0);
    }
  }

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
      <Box sx={{ display: 'flex', width: '100%', flex: 1, alignItems: 'center' }}>
        <CustomerBox>
          {first}
        </CustomerBox>
        <CustomerBox>
          {['+', '-', '*', '/', '%'][operator]}
        </CustomerBox>
        <CustomerBox>
          {second}
        </CustomerBox>
        <CustomerBox>
          =
        </CustomerBox>
        <CustomerBox>
          <TextField variant="outlined" sx={{ width: '50px' }} onChange={checkResult}/>
        </CustomerBox>
      </Box>

      <Button variant="contained" onClick={random} sx={{ marginTop: 2 }}>
        Generate New Problem
      </Button>

      <BottomBar />
    </Box>
  );
}

export default MathPage;