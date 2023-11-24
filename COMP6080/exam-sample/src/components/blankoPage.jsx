import React, {useEffect} from 'react';
import {Box, Grid, TextField} from "@mui/material";


const BlankoPage = () => {

  const [random, setRandom] = React.useState([-1, -1, -1]);
  const [randomData, setRandomData] = React.useState(0);
  const strs = [
    'the fat cats',
    'larger frogs',
    'banana cakes',
    'unsw vs usyd',
    'french toast',
    'hawaii pizza',
    'barack obama',
];


  useEffect(() => {
    setRandomData(Math.floor(Math.random() * strs.length));

    const tempList = [...random];
    let i = 0;
    while (i < 3) {
      const temp = Math.floor(Math.random() * 12);
      if (!tempList.includes(temp) && strs[randomData][temp] !== ' ') {
        tempList[i] = temp;
        i++;
      }
    }
    setRandom(tempList);
  }, []);

  useEffect(() => {
    console.log(random);
  }, [random, randomData]);

  return (
    <Grid container spacing={1} sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', height: '100vh', weight: '100vw'}}>
      {
        strs[randomData].split('').map((char, index) => {
          if (random.includes(index)) {
            return <Grid item xs={1} sx={{ height: 60 }}>
              <Box><TextField type="char" key={index} sx={{ height: 60 }} /></Box>
              </Grid>
          } else {
            return <Grid item xs={1} key={index}>
              <Box sx={{ border: 1, borderColor: 'black', height: 60, display: 'flex', alignItems: 'center', justifyContent: 'center' }}>{char}</Box>
            </Grid>
          }
        })
      }
    </Grid>
  );
}

export default BlankoPage;