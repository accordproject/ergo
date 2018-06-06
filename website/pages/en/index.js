/**
 * Copyright (c) 2017-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const React = require('react');

const CompLibrary = require('../../core/CompLibrary.js');
const MarkdownBlock = CompLibrary.MarkdownBlock; /* Used to read markdown */
const Container = CompLibrary.Container;
const GridBlock = CompLibrary.GridBlock;

const siteConfig = require(process.cwd() + '/siteConfig.js');

function imgUrl(img) {
  return siteConfig.baseUrl + 'img/' + img;
}

function docUrl(doc, language) {
  return siteConfig.baseUrl + 'docs/' + (language ? language + '/' : '') + doc;
}

function pageUrl(page, language) {
  return siteConfig.baseUrl + (language ? language + '/' : '') + page;
}

// fake, static, responsive refmt, lol. See reason.css homeCodeSnippet logic
const pre = "```";
const code = "`";

const codeExampleSmallScreen = `${pre}javascript
clause eathealthy(request : Food) : Outcome {
  enforce request.produce = "apple"
  else return new Outcome{ notice : "You're fired!" };

  emit new Bill{
    billTo: contract.employee,
    amount: request.price * (1.0 + contract.tax / 100.0)
  };
  return new Outcome{ notice : "Very healthy!" }
}
${pre}`;
const codeExampleLargeScreen = codeExampleSmallScreen;

class Button extends React.Component {
  render() {
    return (
      <div className="pluginWrapper buttonWrapper">
        <a className="button" href={this.props.href} target={this.props.target}>
          {this.props.children}
        </a>
      </div>
    );
  }
}

Button.defaultProps = {
  target: '_self',
};

const SplashContainer = props => (
  <div className="homeContainer">
    <div className="homeSplashFade">
      <div className="wrapper homeWrapper">{props.children}</div>
    </div>
  </div>
);

const Logo = props => (
  <div className="projectLogo">
    <img src={props.img_src} />
  </div>
);

const ProjectBanner = props => (
  <div className="homeWrapperInner">
    <div className="homeCodeSnippet">
                <MarkdownBlock>{codeExampleSmallScreen}</MarkdownBlock>
                <MarkdownBlock>{codeExampleLargeScreen}</MarkdownBlock>
    </div>
    <div className="homeTagLine">{siteConfig.tagline}</div>
  </div>
);

const PromoSection = props => (
  <div className="section promoSection">
    <div className="promoRow">
      <div className="pluginRowBlock">{props.children}</div>
    </div>
  </div>
);

class HomeSplash extends React.Component {
  render() {
    let language = this.props.language || '';
    return (
      <SplashContainer>
        <div className="inner">
  <h2 className="projectTitle">
        <img src={imgUrl('ergo.png')} />
  </h2>
          <ProjectBanner />
          <PromoSection>
            <Button href="https://docs.accordproject.org">Accord Project</Button>
            <Button href="#try">Try Online</Button>
            <Button href={
                siteConfig.baseUrl +
                //"docs/" +
                //this.props.language +
                //"/ergo-node.html"
                "docs/ergo-node.html"
              }>Quick Start</Button>
          </PromoSection>
        </div>
      </SplashContainer>
    );
  }
}

const Block = props => (
  <Container
    padding={['bottom', 'top']}
    id={props.id}
    background={props.background}>
    <GridBlock align="center" contents={props.children} layout={props.layout} />
  </Container>
);

const Features = props => (
          <Container className="homeThreePoints paddingBottom">
            <GridBlock
              align="center"
              contents={[
                {
                  title: 'Legal First',
                  content: 'Ergo is designed to capture the legal intent of contracts. Use it to enforce clauses preconditions, manipulate the contract state, and emit obligations.',
                },
                {
                  title: 'Safety and Verification',
                  content: 'Ergo uses functional programming techniques to ensure determinism and prevent errors during contract execution.',
                },
                {
                  title: 'Portable',
                  content: 'Unlike other Smart Contract languages, Ergo is not tied to a specific Blockchain. Write your legal contract logic once, execute it anywhere.',
                },
              ]}
              layout="threeColumn"
            />
          </Container>
);

const TryOut = props => (
  <Block background="light" id="try">
    {[
      {
        content: 'You can try out a live version of Ergo on the <a href="https://accordproject.github.io/ergo-playground">playground</a>. Pick an existing Accord Project legal template and press run to see it execute! Experiment with changes to the logic or the request to see how it affects the contract response.',
        image: imgUrl('playground.png'),
        imageAlign: 'left',
        title: 'Try Online',
      },
    ]}
  </Block>
);

const AccordProject = props => (
  <Block background="dark" id="accord">
    {[
      {
        content: 'Write the logic for [Accord Project](https://docs.accordproject.org) legal templates in Ergo. Use [Accord Project Cicero](https://docs.accordproject.org/docs/cicero.html) to bind contracts in natural language to their logic and execute them on the cloud or a blockchain platform.',
        image: imgUrl('template.png'),
        imageAlign: 'right',
        title: 'Accord Project',
      },
    ]}
  </Block>
);

const Showcase = props => {
  if ((siteConfig.users || []).length === 0) {
    return null;
  }
  const showcase = siteConfig.users
    .filter(user => {
      return user.pinned;
    })
    .map((user, i) => {
      return (
        <a href={user.infoLink} key={i}>
          <img src={user.image} alt={user.caption} title={user.caption} />
        </a>
      );
    });

  return (
    <div className="productShowcaseSection paddingBottom">
      <h2>{"Who's Using This?"}</h2>
      <div className="logos">{showcase}</div>
      <div className="more-users">
        <a className="button" href={pageUrl('users.html', props.language)}>
          More {siteConfig.title} Users
        </a>
      </div>
    </div>
  );
};

class Index extends React.Component {
  render() {
    let language = this.props.language || '';

    return (
      <div>
        <HomeSplash language={language} />
        <div className="mainContainer">
          <Features />
          <AccordProject />
          <TryOut />
          <Showcase language={language} />
        </div>
      </div>
    );
  }
}

module.exports = Index;
