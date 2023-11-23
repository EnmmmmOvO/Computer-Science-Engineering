import React from 'react';
import logo from './logo.svg';
import './App.css';

function App() {
  const [welcomeText, setWelcomeText] = React.useState('');
  const [welcomeError, setWelcomeError] = React.useState(false);
  const [emails, setEmails] = React.useState(['', '']);
  const [summaryScreen, setSummaryScreen] = React.useState(false);

  const messageBlur = () => {
    if (welcomeText === '') {
      setWelcomeError(true);
    }
  }

  const messageFocus = () => {
    setWelcomeError(false);
  };

  const messageKeyUp = (e) => {
    setWelcomeText(e.target.value);
  };

  const addMore = () => {
    const newEmails = [...emails];
    newEmails.push('', '');
    setEmails(newEmails);
  };

  const emailCapture = (e, idx) => {
    const newEmails = [...emails];
    newEmails[idx] = e.target.value;
    setEmails(newEmails);
  }

  return (
    <div className="form-body">
      {
        summaryScreen ? <>
          <div onClick={function () { setSummaryScreen(false) }}>❌ Close</div>
          Summary Screen!<br />
          Welcome message: {welcomeText}<br />
          Emails:<br />
            {emails.map((email, idx) => {
              if (email) {
                return <>
                  &nbsp;&nbsp;Email {idx + 1}: email<br />
                </>
              }
            })}
        </> : <>
          <h2>Please invite your friends to join CSE</h2>
          <div>
            Welcome Message:<br />
            <textarea
              onBlur={messageBlur}
              onFocus={messageFocus}
              onKeyUp={messageKeyUp}
              style={{
                background: welcomeError ? 'red' : 'white'
              }}
            ></textarea><br />
          </div>
          {welcomeText && (
            <div>
              <h3>Emails</h3>
              {emails.map(function (email, idx) {
                return <>
                  Email {idx + 1}:
                  <input
                    type="text"
                    onChange={function (event) {
                      emailCapture(event, idx);
                    }}
                    value={email}
                  />
                  <br />    
                </>
              })}
              {emails.length < 10 && emails.length === emails.filter(v => v !== '').length &&
                <button
                  type="button"
                  onClick={addMore}
                >
                  Add more
                </button>
              }
              <button disabled={emails.filter(v => v !== '').length === 0} type="button" onClick={function () {
                setEmails([...emails].map(v => ''));
              }}>Reset</button>
            </div>
          )}
          <br />
          <button
            type="button"
            onClick={function () {
              setSummaryScreen(true);
            }}
            disabled={welcomeText === '' || emails.filter(v => v !== '').length === 0}
          >
            Submit
          </button>
        </>
      }
    </div>
  );
}

export default App;
