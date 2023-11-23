import { Link } from "react-router-dom";

const Home = () => {
  // Generates a random integer between 100 and 1
  const generateRndInt = () => {
    return Math.floor(Math.random() * (100 - 1) + 1);
  };

  return (
    <>
      <h1>Random Post Navigator</h1>
      <Link to={`/post/${generateRndInt()}`}>
        Click here to go to a random post!
      </Link>
    </>
  );
};

export default Home;
