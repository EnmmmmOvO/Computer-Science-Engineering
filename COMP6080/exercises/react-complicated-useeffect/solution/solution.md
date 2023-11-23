1. If there is no dependency array, how many times will `effectRerender` update?

> An infinite number of times.

> If there is no dependency array, the callback function will run every time there is a re-render. During the first page render, the callback function will run, and `effectRerender` will increment. This triggers another re-render, as the `effectRerender` variable is a React state variable represented in the DOM. As the DOM re-renders, the callback function will run again. This will repeat (effectively forever).

2. If there is an empty dependency array (`[]`), how many times will `effectRerender` update upon initial render? How many times will `effectRerender` update when you increment `aRerender` or `bRerender`?

> Once. 

> How `useEffect` works is that, after the initial render, the callback function will run every time the variables in the dependency array change. As there is nothing in the dependency array, `effectRerender` will only increment once (During the initial page render).

3. If there is a dependency array with `aRerender` (`[aRerender]`), how many times will `effectRerender` update?

>`aRerender + 1`

>`+ 1` because `useEffect` runs the callback function upon initial render.

4. If there is a dependency array with both `aRerender` and `bRerender` (`[aRerender, bRerender]`), how many times will `effectRerender` update?

>`aRerender + bRerender + 1`

