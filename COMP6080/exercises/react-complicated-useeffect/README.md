## A complicated example with useEffect 

In the `react` folder, there is a basic React app that will show the basics of the `useEffect` hook. In the file, there are two React state variables (`aRerender` and `bRerender`) which keep track of how many times they re-render. There is also another React state variable (`effectRerender`) that keeps track of how many times the DOM mutates and renders using the React `useEffect` hook.

Write a React `useEffect` hook with a callback function that increments the `effectRerender` variable. Do not include a dependency array for now.

Refresh between changing the dependency arrays, to reset the counters.

1. If there is no dependency array, how many times will `effectRerender` update?

2. If there is an empty dependency array (`[]`), how many times will `effectRerender` update upon initial render? How many times will `effectRerender` update when you increment `aRerender` or `bRerender`?

3. If there is a dependency array with `aRerender` (`[aRerender]`), how many times will `effectRerender` update?

4. If there is a dependency array with both `aRerender` and `bRerender` (`[aRerender, bRerender]`), how many times will `effectRerender` update?

